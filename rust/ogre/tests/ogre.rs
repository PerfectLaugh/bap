use ogre::*;

type Fields = (
    Field<i64>,
    Field<i64>,
    Field<i64>,
    Field<i64>,
    Field<String>,
);
type Corpus = (
    Document,
    Attribute<Vec<i64>>,
    Attribute<Vec<i64>>,
    Attribute<Vec<i64>>,
    Field<i64>,
    Field<i64>,
    Field<i64>,
    Field<i64>,
);

fn fields() -> Fields {
    (
        Field::int("id"),
        Field::int("key"),
        Field::int("x"),
        Field::int("y"),
        Field::str("z"),
    )
}
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
                    Scalar::Int(x) => Ok(*x),
                    _ => Err(Error::Query("expected int".into())),
                })
                .collect()
        },
    )
}
fn doc(seed: u64, n: i64) -> Corpus {
    let (id, key, x, y, _) = fields();
    let a = int_attr("a", vec![id.clone(), key.clone(), x.clone()]);
    let b = int_attr("b", vec![id.clone(), key.clone(), y.clone()]);
    let c = int_attr("c", vec![id.clone(), y.clone(), Field::int("z")]);
    let mut doc = Document::new();
    let mut state = seed;
    let mut small = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((state >> 32) % 4) as i64
    };
    for i in 0..n {
        doc.insert(&a, vec![i, small(), small()]).unwrap();
        doc.insert(&b, vec![i, small(), small()]).unwrap();
        doc.insert(&c, vec![i, small(), small()]).unwrap();
    }
    (doc, a, b, c, id, key, x, y)
}

#[test]
fn indexed_joins_match_filtered_products() {
    for seed in 0..10 {
        let (doc, a, b, c, _, key, x, y) = doc(seed, 12);
        let joined = Query::new(Selection::one(&a).and(&b).and(&c))
            .join(vec![
                Join::new(vec![Join::unqualified(&key)]),
                Join::new(vec![Join::qualified(&b, &y), Join::qualified(&c, &y)]),
            ])
            .where_expr(Expr::field(&a, &x).lt(Expr::int(3)))
            .execute(&doc)
            .unwrap();
        let filtered = Query::new(Selection::one(&a).and(&b).and(&c))
            .where_expr(
                Expr::field(&a, &key)
                    .eq(Expr::field(&b, &key))
                    .and(Expr::field(&b, &y).eq(Expr::field(&c, &y)))
                    .and(Expr::field(&a, &x).lt(Expr::int(3))),
            )
            .execute(&doc)
            .unwrap();
        let ids = |rows: &[Row]| {
            rows.iter()
                .map(|row| {
                    (
                        row.get::<Vec<i64>>(0, &a).unwrap()[0],
                        row.get::<Vec<i64>>(1, &b).unwrap()[0],
                        row.get::<Vec<i64>>(2, &c).unwrap()[0],
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(ids(&joined), ids(&filtered));
        assert!(!joined.is_empty());
    }
}

#[test]
fn backward_and_self_joins_work() {
    let (doc, _, b, c, _, _, _, y) = doc(4, 12);
    let joined = Query::new(Selection::one(&c).and(&b))
        .join(vec![Join::new(vec![
            Join::qualified(&c, &y),
            Join::qualified(&b, &y),
        ])])
        .execute(&doc)
        .unwrap();
    let filtered = Query::new(Selection::one(&c).and(&b))
        .where_expr(Expr::field(&c, &y).eq(Expr::field(&b, &y)))
        .execute(&doc)
        .unwrap();
    assert_eq!(joined.len(), filtered.len());
    let same = Query::new(Selection::one(&b).and(&b))
        .join(vec![Join::new(vec![
            Join::positional(0, &y),
            Join::positional(1, &y),
        ])])
        .execute(&doc)
        .unwrap();
    assert!(same.iter().all(
        |row| row.get::<Vec<i64>>(0, &b).unwrap()[2] == row.get::<Vec<i64>>(1, &b).unwrap()[2]
    ));
}

#[test]
fn document_round_trip_normalizes_and_deduplicates() {
    let text = r#"
      ; a comment
      (declare student (name str) (gpa float) (age int) (enrolled bool))
      (student (name "Jane Doe") (gpa 3.50) (age 0x15) (enrolled true))
      (student "John" 3.5 20 false)
      (student "John" 3.50 20 false)
    "#;
    let doc = Document::parse(text).unwrap();
    assert_eq!(doc.definitions(), 2);
    assert_eq!(doc.declarations(), 1);
    assert!(
        doc.to_string()
            .contains("(student \"Jane Doe\" 3.5 21 true)")
    );
    assert_eq!(Document::parse(&doc.to_string()).unwrap(), doc);
    assert!(doc.to_yaml().contains("scheme:"));
    assert!(Document::parse("(declare a (x int)) (a nope)").is_err());
    assert!(Document::parse("(a 1)").is_err());
    assert!(Document::parse("(declare a (x int)) (a (x 1) (x 2))").is_err());
    assert!(Document::parse("\"unterminated").is_err());
}

#[test]
fn request_require_and_merge_check_cardinality() {
    let field = Field::<i64>::int("id");
    let attr = int_attr("item", vec![field]);
    let mut left = Document::new();
    left.insert(&attr, vec![1]).unwrap();
    assert_eq!(left.require(&attr).unwrap(), vec![1]);
    left.insert(&attr, vec![2]).unwrap();
    assert!(left.require(&attr).is_err());
    assert_eq!(left.require_that(&attr, |x| x[0] == 2).unwrap(), vec![2]);
    let mut right = Document::new();
    right.insert(&attr, vec![3]).unwrap();
    assert_eq!(left.merge(&right).unwrap().definitions(), 3);
}

#[test]
fn scalar_expressions_are_simplified_and_checked() {
    assert_eq!(Expr::int(2) + Expr::int(3), Expr::int(5));
    assert_eq!(Expr::int(5) - Expr::int(3), Expr::int(2));
    assert_eq!(
        Expr::bool(true).implies(Expr::bool(false)),
        Expr::bool(false)
    );
    assert_eq!(Expr::str("a").lt(Expr::str("b")), Expr::bool(true));
}

#[test]
fn prepared_queries_stream_and_serde_restores_lazy_rows() {
    let (doc, a, b, _, _, key, _, _) = doc(9, 24);
    let query =
        Query::new(Selection::one(&a).and(&b)).join(vec![Join::new(vec![Join::unqualified(&key)])]);
    let prepared = query.prepare(&doc).unwrap();
    let expected = prepared.execute().unwrap().len();
    assert_eq!(prepared.execute().unwrap().len(), expected);
    let mut streamed = 0;
    prepared
        .for_each(|row| {
            assert_eq!(row.get::<Vec<i64>>(0, &a).unwrap().len(), 3);
            streamed += 1;
            Ok(())
        })
        .unwrap();
    assert_eq!(streamed, expected);

    let restored = Document::from_json(&doc.to_json().unwrap()).unwrap();
    assert_eq!(restored, doc);
    let prepared = query.prepare(&restored).unwrap();
    assert_eq!(prepared.execute().unwrap().len(), expected);
    assert!(Document::from_json("{").is_err());
}

#[test]
fn float_join_keys_are_exact() {
    let id = Field::<f64>::float("id");
    let attr = Attribute::new(
        "float",
        Schema::default().field(&id),
        |values: &Vec<f64>| Ok(vec![Scalar::Float(values[0])]),
        |values| match values {
            [Scalar::Float(value)] => Ok(vec![*value]),
            _ => Err(Error::Query("expected float".into())),
        },
    );
    let mut doc = Document::new();
    doc.insert(&attr, vec![1.5]).unwrap();
    doc.insert(&attr, vec![f64::NAN]).unwrap();
    let prepared = Query::new(Selection::one(&attr).and(&attr))
        .join(vec![Join::new(vec![Join::unqualified(&id)])])
        .prepare(&doc)
        .unwrap();
    assert_eq!(prepared.execute().unwrap().len(), 2);
}
