/// Fuzzing tests for interner.
///
/// The fuzzing tests are heavy, and best run one at a time.
///
/// Reminder: to run only fuzzing tests, run `cargo test --test fuzz`.
use std::{cmp, collections::HashMap, fmt};

use bursty::BurstyBuilder;

use endor_interner::{Interner, StringId};

//  Change this variable to use a different number of threads.
const NUMBER_THREADS: usize = 8;

#[test]
fn single_word() {
    //  The simplest fuzz test: attempt a single insertion, coordinated across all threads.

    const MAMA_MIA: &str = "Mama mia!";

    for _ in 0..512 {
        let locals: Vec<Option<StringId>> = vec![None; NUMBER_THREADS];

        let mut builder = BurstyBuilder::new(Interner::new().unwrap(), locals);

        builder.add_simple_step(|| {
            |interner, local| {
                *local = Some(interner.insert_str(MAMA_MIA).unwrap());
            }
        });

        let bursty = builder.launch(1);

        let interner = bursty.global();
        let locals: Vec<_> = bursty.into_locals().into_iter().flatten().collect();

        assert_eq!(MAMA_MIA, interner.get_str(locals[0]).unwrap());
        assert!(locals.windows(2).all(|window| window[0] == window[1]), "{locals:?}");
    }
}

//  Too expensive for MIRI to run.
#[cfg(not(miri))]
#[test]
fn shakespeare_words_all_order() {
    //  A more idiomatic test: attempt to insert the same sequence of words, coordinated across all threads.
    //
    //  There are many duplicates, and therefore many insertions should actually turn into simple reads. Assuming fair
    //  scheduling it is nonetheless expected that threads will catch up with thread actually performing an insertion
    //  and therefore contention will occur.

    let locals: Vec<Vec<StringId>> = vec![Vec::new(); NUMBER_THREADS];

    let mut builder = BurstyBuilder::new(Interner::new().unwrap(), locals);

    let words = shakespeare::get_words();

    builder.add_simple_step(|| {
        move |interner, local| {
            for word in words {
                let id = interner.insert_str(word).unwrap();

                local.push(id);
            }
        }
    });

    let bursty = builder.launch(1);

    let interner = bursty.global();
    let locals: Vec<_> = bursty.into_locals();

    //  All threads should have the same result.
    assert_all_identical(&locals);

    let sample = &locals[0];

    //  There should be exactly one StringId per word, and it should retrieve this word.
    assert_word_recovery(&interner, words, sample);

    //  There should be exactly one StringId per unique word.
    assert_deduplication(words, sample);
}

//  Too expensive for MIRI to run.
#[cfg(not(miri))]
#[test]
fn shakespeare_unique_all_order() {
    //  A high-contention test: attempt to insert the same sequence of words, guaranteed without duplicate, across all
    //  threads.
    //
    //  The absence of duplicate means that each insertion requires one of the thread to perform it... and therefore
    //  collide with all the others also attempting. Any thread lagging behind should find itself catching up by virtue
    //  of not actually having to perform any insertion, hence contention should run high.

    let locals: Vec<Vec<StringId>> = vec![Vec::new(); NUMBER_THREADS];

    let mut builder = BurstyBuilder::new(Interner::new().unwrap(), locals);

    let words = shakespeare::get_unique_words();

    builder.add_simple_step(|| {
        move |interner, local| {
            for word in words {
                let id = interner.insert_str(word).unwrap();

                local.push(id);
            }
        }
    });

    let bursty = builder.launch(1);

    let interner = bursty.global();
    let locals: Vec<_> = bursty.into_locals();

    //  All threads should have the same result.
    assert_all_identical(&locals);

    let sample = &locals[0];

    //  There should be exactly one StringId per word, and it should retrieve this word.
    assert_word_recovery(&interner, words, sample);
}

#[track_caller]
fn assert_all_identical<T>(elements: &[T])
where
    T: cmp::PartialEq + fmt::Debug,
{
    assert!(elements.windows(2).all(|window| window[0] == window[1]), "{elements:?}");
}

#[track_caller]
fn assert_word_recovery(interner: &Interner, words: &[&str], ids: &[StringId]) {
    assert_eq!(words.len(), ids.len());

    for (index, (word, id)) in words.iter().zip(ids).enumerate() {
        let actual = interner.get_str(*id).unwrap();

        assert_eq!(*word, actual, "difference on {index}th word");
    }
}

#[track_caller]
fn assert_deduplication(words: &[&str], ids: &[StringId]) {
    let occurrences = {
        let mut occurrences = HashMap::new();

        for (index, &word) in words.iter().enumerate() {
            occurrences.entry(word).or_insert(Vec::new()).push(index);
        }

        occurrences
    };

    for (word, indexes) in occurrences {
        let resampled: Vec<_> = indexes.into_iter().map(|index| ids[index]).collect();

        assert!(
            resampled.windows(2).all(|window| window[0] == window[1]),
            "difference in StringIds of {word}: {resampled:?}"
        );
    }
}

//  Work of shakespeare, in two forms:
//  -   A sequence of words, as per the original file.
//  -   A sequence of _unique_ words, in the same order as above, minus duplicates.
mod shakespeare {
    use std::{collections::HashSet, fs, sync::OnceLock};

    static SHAKESPEARE_WORK: OnceLock<String> = OnceLock::new();

    static SHAKESPEARE_WORDS: OnceLock<Vec<&'static str>> = OnceLock::new();

    static SHAKESPEARE_UNIQUE: OnceLock<Vec<&'static str>> = OnceLock::new();

    pub(super) fn get_words() -> &'static [&'static str] {
        SHAKESPEARE_WORDS.get_or_init(|| get_work().split(|c: char| c.is_ascii_alphanumeric()).collect())
    }

    pub(super) fn get_unique_words() -> &'static [&'static str] {
        SHAKESPEARE_UNIQUE.get_or_init(|| {
            let mut seen = HashSet::new();
            let mut dedup = Vec::new();

            for &word in get_words() {
                if seen.insert(word) {
                    dedup.push(word);
                }
            }

            dedup
        })
    }

    fn get_work() -> &'static str {
        SHAKESPEARE_WORK.get_or_init(|| fs::read_to_string("etc/shakespeare.txt").unwrap())
    }
}
