use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hashmap::HashMap;

fn prefill_hashmap() -> HashMap<i32, i32> {
    let mut new_hash = HashMap::new();
    for (i, j) in (0..100_000).zip(100_000..200_000) {
        new_hash.insert(i, j);
    }
    new_hash
}

fn mass_insert() {
    prefill_hashmap();
}

fn mass_remove(map: &mut HashMap<i32, i32>) {
    for i in 0..100_000 {
        map.remove(&i);
    }
}

fn get_two(map: &mut HashMap<i32, i32>) {
    let _in_map = map.get(&500);
    let _not_in_map = map.get(&100_500);
}

pub fn bench_basic_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("Basic Ops");

    group.bench_function("Insert", |b| {
        b.iter(|| black_box(mass_insert()));
    });

    let mut remove_map = prefill_hashmap();
    group.bench_function("Remove", |b| {
        b.iter(|| black_box(mass_remove(&mut remove_map)));
    });

    let mut get_map = prefill_hashmap();
    group.bench_function("Get", |b| {
        b.iter(|| black_box(get_two(&mut get_map)));
    });

    group.finish();
}

pub fn bench_iterators(c: &mut Criterion) {
    let mut group = c.benchmark_group("Iterators");
    let mut walker = prefill_hashmap();
    group.bench_function("Values", |b| {
        b.iter(|| {
            black_box(walker.values().count());
        })
    });
    group.bench_function("Keys", |b| {
        b.iter(|| {
            black_box(walker.keys().count());
        })
    });
    group.bench_function("Iter", |b| {
        b.iter(|| {
            black_box(walker.iter().count());
        })
    });
    group.bench_function("Iter Mut ", |b| {
        b.iter(|| {
            black_box(walker.iter_mut().count());
        })
    });

    group.finish();
}

criterion_group!(benches, bench_basic_ops, bench_iterators);
criterion_main!(benches);
