use ogre::{Attribute, Document, Expr, Field, Join, Query, Scalar, Schema, Selection};
use std::time::Instant;

const ROWS: i64 = 200;
const QUERIES: usize = 10;

fn int_attr(name: &str, fields: Vec<Field<i64>>) -> Attribute<Vec<i64>> {
    let schema = fields
        .iter()
        .fold(Schema::default(), |schema, field| schema.field(field));
    Attribute::new(
        name,
        schema,
        |values: &Vec<i64>| Ok(values.iter().copied().map(Scalar::Int).collect()),
        |values| {
            values
                .iter()
                .map(|value| match value {
                    Scalar::Int(value) => Ok(*value),
                    _ => panic!("integer schema"),
                })
                .collect()
        },
    )
}

fn main() {
    let start = Instant::now();
    let id = Field::<i64>::int("id");
    let key = Field::<i64>::int("key");
    let x = Field::<i64>::int("x");
    let y = Field::<i64>::int("y");
    let a = int_attr("a", vec![id.clone(), key.clone(), x.clone()]);
    let b = int_attr("b", vec![id, key.clone(), y.clone()]);
    let c = int_attr(
        "c",
        vec![Field::<i64>::int("cid"), y.clone(), Field::<i64>::int("z")],
    );
    let mut document = Document::new();
    let mut random = 7_u64;
    let mut small = || {
        random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((random >> 32) & 3) as i64
    };
    for index in 0..ROWS {
        document.insert(&a, vec![index, small(), small()]).unwrap();
        document.insert(&b, vec![index, small(), small()]).unwrap();
        document.insert(&c, vec![index, small(), small()]).unwrap();
    }
    println!(
        "ogre_setup,{:.9},{}",
        start.elapsed().as_secs_f64(),
        ROWS * 3
    );
    let query = Query::new(Selection::one(&a).and(&b).and(&c))
        .join(vec![
            Join::new(vec![Join::unqualified(&key)]),
            Join::new(vec![Join::qualified(&b, &y), Join::qualified(&c, &y)]),
        ])
        .where_expr(Expr::field(&a, &x).lt(Expr::int(3)));
    let query = query.prepare(&document).unwrap();
    let start = Instant::now();
    let mut rows = 0_usize;
    let mut checksum = 0_i64;
    for _ in 0..QUERIES {
        query
            .for_each(|row| {
                rows += 1;
                checksum += row.get::<Vec<i64>>(0, &a).unwrap()[0];
                checksum += row.get::<Vec<i64>>(1, &b).unwrap()[0];
                checksum += row.get::<Vec<i64>>(2, &c).unwrap()[0];
                Ok(())
            })
            .unwrap();
    }
    println!(
        "ogre_query,{:.9},{QUERIES},{rows},{checksum}",
        start.elapsed().as_secs_f64()
    );
}
