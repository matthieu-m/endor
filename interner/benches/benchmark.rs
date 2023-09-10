//! Benchmarks of endor-interner.

use std::time::{Duration, Instant};

use bursty::BurstyBuilder;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fxhash::FxHashSet;

use endor_interner::Interner;

criterion_main!(control, single_threaded, multi_threaded,);

//  Sample results on 8 cores/16 threads.
//
//                                                      Total           Average/word
//
//  control all (3794116)                               23.127ms          6.1ns
//  control unique (1516)                                   12.709µs      8.4ns
//
//  single-threaded all (3794116)                       42.893ms         11ns
//  single-threaded unique (1516)                           55.039µs     36ns
//
//  multi-threaded replicas all (3794116 each) 2T       44.088ms         11ns
//  multi-threaded replicas all (3794116 each) 4T       54.794ms         14ns
//  multi-threaded replicas all (3794116 each) 8T       77.785ms         20ns
//
//  multi-threaded replicas unique (1516 each) 2T          112.18µs      74ns
//  multi-threaded replicas unique (1516 each) 4T          118.00µs      77ns
//  multi-threaded replicas unique (1516 each) 8T          140.40µs      93ns
//
//  multi-threaded coop all (1897058 each) 2T           22.704ms         12ns
//  multi-threaded coop all ( 948529 each) 4T           12.134ms         13ns
//  multi-threaded coop all ( 474264 each) 8T            9.263ms         20ns
//
//  multi-threaded coop unique (758 each) 2T                63.291µs     83ns
//  multi-threaded coop unique (379 each) 4T                39.711µs    105ns
//  multi-threaded coop unique (189 each) 8T                29.772µs    158ns

criterion_group!(control, control_all, control_unique,);

//  Time to insert all words of the work of shakespeare (3,794,116) in a pre-sized FxHashSet.
//
//  This benchmark represents the performance goal, it uses the same hashing algorithm and principle, without the
//  overhead of atomic operations nor having to copy the strings.
fn control_all(c: &mut Criterion) {
    control_impl(c, "control all", shakespeare::get_words());
}

//  Time to insert all unique words of the work of shakespeare (1,516) in a pre-sized FxHashSet.
//
//  This benchmark represents the performance goal, it uses the same hashing algorithm and principle, without the
//  overhead of atomic operations nor having to copy the strings.
fn control_unique(c: &mut Criterion) {
    control_impl(c, "control unique", shakespeare::get_unique_words());
}

fn control_impl(c: &mut Criterion, root: &str, words: &'static [&'static str]) {
    let name = format!("{root} ({})", words.len());
    let unique = shakespeare::get_unique_words().len();

    c.bench_function(&name, |b| {
        b.iter(|| {
            let mut map = FxHashSet::default();
            map.reserve(unique);

            for word in words {
                map.insert(word);
            }

            black_box(map)
        })
    });
}

criterion_group!(single_threaded, single_threaded_all, single_threaded_unique);

//  Time to insert all words of the work of shakespeare (3,794,116) in a single thread.
fn single_threaded_all(c: &mut Criterion) {
    let words = shakespeare::get_words();
    let name = format!("single-threaded all ({})", words.len());

    c.bench_function(&name, |b| b.iter(|| single_threaded_impl(words)));
}

//  Time to insert all unique words of the work shakespeare (1,516) in a single thread.
fn single_threaded_unique(c: &mut Criterion) {
    let words = shakespeare::get_unique_words();
    let name = format!("single-threaded unique ({})", words.len());

    c.bench_function(&name, |b| b.iter(|| single_threaded_impl(words)));
}

fn single_threaded_impl(words: &[&str]) {
    let interner = Interner::new().unwrap();

    for word in words {
        let result = interner.insert_str(word);

        let _ = black_box(result);
    }
}

criterion_group!(
    multi_threaded,
    multi_threaded_replicas_all,
    multi_threaded_replicas_unique,
    multi_threaded_coop_all,
    multi_threaded_coop_unique,
);

//  Worst time to insert all words of the work of shakespeare (3,794,116) by N threads in parallel.
//
//  Many collisions.
fn multi_threaded_replicas_all(c: &mut Criterion) {
    multi_threaded_replicas_impl(c, "multi-threaded replicas all", shakespeare::get_words());
}

//  Worst time to insert all unique words of the work of shakespeare (1,516) by N threads in parallel.
//
//  All collisions.
fn multi_threaded_replicas_unique(c: &mut Criterion) {
    multi_threaded_replicas_impl(c, "multi-threaded replicas unique", shakespeare::get_unique_words());
}

//  Worst time to insert 1/N words of the work of shakespeare (3,794,116) by N threads in parallel.
//
//  Collisions are occasional.
fn multi_threaded_coop_all(c: &mut Criterion) {
    multi_threaded_coop_impl(c, "multi-threaded coop all", shakespeare::get_words());
}

//  Worst time to insert 1/N unique words of the work of shakespeare (1,516) by N threads in parallel.
//
//  No true collisions, but hash collisions.
fn multi_threaded_coop_unique(c: &mut Criterion) {
    multi_threaded_coop_impl(c, "multi-threaded coop unique", shakespeare::get_unique_words());
}

const NUMBER_THREADS: [usize; 3] = [2, 4, 8];

fn multi_threaded_replicas_impl(c: &mut Criterion, root: &str, words: &'static [&'static str]) {
    for threads in NUMBER_THREADS {
        let name = format!("{root} ({} each) {threads}T", words.len());

        c.bench_function(&name, |b| {
            b.iter_custom(|n| {
                let mut elapsed = Duration::default();

                for _ in 0..n {
                    let locals: Vec<_> = vec![Duration::default(); threads];

                    let mut builder = BurstyBuilder::new(Interner::new().unwrap(), locals);

                    builder.add_simple_step(|| {
                        move |interner, local| {
                            let start = Instant::now();

                            for word in words {
                                let result = interner.insert_str(word);

                                let _ = black_box(result);
                            }

                            *local = start.elapsed();
                        }
                    });

                    let bursty = builder.launch(1);
                    let locals = bursty.into_locals();

                    elapsed += locals.into_iter().max().unwrap();
                }

                elapsed
            })
        });
    }
}

fn multi_threaded_coop_impl(c: &mut Criterion, root: &str, words: &'static [&'static str]) {
    for threads in NUMBER_THREADS {
        let name = format!("{root} ({} each) {threads}T", words.len() / threads);

        c.bench_function(&name, |b| {
            b.iter_custom(|n| {
                let mut elapsed = Duration::default();

                for _ in 0..n {
                    let n_words = words.len() / threads;

                    let locals: Vec<_> = (0..threads)
                        .map(|i| {
                            let words = &words[(i * n_words)..((i + 1) * n_words)];

                            (Duration::default(), words)
                        })
                        .collect();

                    let mut builder = BurstyBuilder::new(Interner::new().unwrap(), locals);

                    builder.add_simple_step(|| {
                        move |interner, local| {
                            let start = Instant::now();

                            for word in local.1 {
                                let result = interner.insert_str(word);

                                let _ = black_box(result);
                            }

                            local.0 = start.elapsed();
                        }
                    });

                    let bursty = builder.launch(1);
                    let locals = bursty.into_locals();

                    elapsed += locals.into_iter().map(|t| t.0).max().unwrap();
                }

                elapsed
            })
        });
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
