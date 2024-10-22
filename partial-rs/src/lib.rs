use std::{
    collections::{BTreeMap, HashMap},
    hash::{BuildHasher, Hash},
};

pub use partial_rs_derive::Partial;

pub trait Diff {
    type Orig: IntoPartial<Partial = Self>;

    /// Returns difference between new and old structs/enums.
    /// If variants in new and old enums are different then variant from new is returned.
    fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self>
    where
        Self: Sized;
}

impl<T> Diff for Vec<T>
where
    <T as Diff>::Orig: Clone,
    T: Diff + ToOwned + Clone,
{
    type Orig = Vec<T::Orig>;

    fn diff(_old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
        Some(new.iter().map(|d| d.to_partial()).collect::<Vec<_>>())
    }
}

impl<T> Diff for Option<T>
where
    <T as Diff>::Orig: Clone,
    T: Diff + ToOwned + Clone,
{
    type Orig = Option<T::Orig>;

    fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
        Some(match (old, new) {
            (Some(old), Some(new)) => T::diff(old, new),
            (_, new) => new.clone().map(|d| d.to_partial()),
        })
    }
}

impl<K, V, S> Diff for HashMap<K, V, S>
where
    <V as Diff>::Orig: Clone,
    K: Hash + Eq + Clone,
    V: Diff + Clone,
    S: Default + BuildHasher,
{
    type Orig = HashMap<K, V::Orig, S>;

    fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
        let mut diffed: HashMap<K, V, S> = HashMap::with_hasher(S::default());
        for (k, new_v) in new.iter() {
            if let Some(old_v) = old.get(k) {
                if let Some(difference) = V::diff(old_v, new_v) {
                    diffed.insert(k.clone(), difference);
                }
            } else {
                diffed.insert(k.clone(), new_v.to_partial());
            }
        }
        if diffed.is_empty() {
            None
        } else {
            Some(diffed)
        }
    }
}

impl<K, T> Diff for BTreeMap<K, T>
where
    <T as Diff>::Orig: Clone,
    K: Ord + Clone,
    T: Diff + Clone,
{
    type Orig = BTreeMap<K, T::Orig>;

    fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
        let mut diffed: BTreeMap<K, T> = BTreeMap::new();
        for (k, new_v) in new.iter() {
            if let Some(old_v) = old.get(k) {
                if let Some(difference) = T::diff(old_v, new_v) {
                    diffed.insert(k.clone(), difference);
                }
            } else {
                diffed.insert(k.clone(), new_v.clone().into_partial());
            }
        }

        if diffed.is_empty() {
            None
        } else {
            Some(diffed)
        }
    }
}

pub trait IntoPartial {
    type Partial;

    fn into_partial(self) -> Self::Partial;
}

pub trait ToPartial: IntoPartial {
    fn to_partial(&self) -> Self::Partial;
}

impl<T> ToPartial for T
where
    T: IntoPartial + Clone,
{
    fn to_partial(&self) -> Self::Partial {
        self.to_owned().into_partial()
    }
}

/// Wrapper for #[partial(recursive)] attr
pub struct Recursive<T>(pub T);

impl<T: IntoPartial> IntoPartial for Recursive<T> {
    type Partial = T::Partial;

    fn into_partial(self) -> Self::Partial {
        self.0.into_partial()
    }
}

impl<T: IntoPartial> IntoPartial for Option<T> {
    type Partial = Option<T::Partial>;

    fn into_partial(self) -> Self::Partial {
        self.map(|t| t.into_partial())
    }
}

impl<T: IntoPartial> IntoPartial for Vec<T> {
    type Partial = Vec<T::Partial>;

    fn into_partial(self) -> Self::Partial {
        self.into_iter().map(T::into_partial).collect()
    }
}

impl<K: Hash + Eq, V: IntoPartial, S: Default + BuildHasher> IntoPartial for HashMap<K, V, S> {
    type Partial = HashMap<K, V::Partial, S>;

    fn into_partial(self) -> Self::Partial {
        self.into_iter()
            .map(|(key, value)| (key, value.into_partial()))
            .collect()
    }
}

impl<K: Ord, T: IntoPartial> IntoPartial for BTreeMap<K, T> {
    type Partial = BTreeMap<K, T::Partial>;

    fn into_partial(self) -> Self::Partial {
        self.into_iter()
            .map(|(key, value)| (key, value.into_partial()))
            .collect()
    }
}

#[cfg(test)]
mod test {
    use crate::IntoPartial;

    use super::{Diff, Partial, ToPartial};
    use std::collections::{BTreeMap, HashMap};

    #[test]
    fn derive_struct() {
        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField3 {
            #[partial(skip)]
            field1: String,
            field2: String,
        }

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField4 {
            #[partial(skip)]
            field1: String,
            field2: String,
        }

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct Test {
            field1: String, // -> Option<String>

            #[partial(skip)]
            field2: String, // -> String

            #[partial(recursive)]
            field3: HashMap<i32, TestField3>, // ->  Option<HashMap<i32, TestField3Partial>>

            #[partial(skip, recursive)]
            field4: TestField4, // ->  TestField4Partial

            #[partial(skip, recursive)]
            field5: Option<TestField4>, // ->  Option<TestField4Partial>
        }

        let instance = Test {
            field1: "f1".to_string(),
            field2: "f2".to_string(),
            field3: {
                let mut map = HashMap::new();
                map.insert(
                    42,
                    TestField3 {
                        field1: "f3f1".to_string(),
                        field2: "f3f2".to_string(),
                    },
                );
                map
            },
            field4: TestField4 {
                field1: "f4f1".to_string(),
                field2: "f4f2".to_string(),
            },
            field5: Some(TestField4 {
                field1: "f5f1".to_string(),
                field2: "f5f2".to_string(),
            }),
        };

        let partial = instance.to_partial();
        let mut modified = instance.clone();

        modified.field5 = Some(TestField4 {
            field1: "f5f1".to_string(),
            field2: "fpf2-modified".to_string(),
        });
        let diff = TestPartial::diff(&instance, &modified).unwrap();
        assert_eq!(diff.field5.unwrap().field2.unwrap(), "fpf2-modified");

        assert_eq!(partial.field1, Some(instance.field1));
        assert_eq!(partial.field2, instance.field2);
        assert_eq!(
            partial.field5.map(|f| f.field2),
            instance.field5.map(|f| Some(f.field2))
        );

        let f3 = partial.field3.clone().unwrap();
        let mut iter = f3.into_iter().zip(instance.field3.clone());
        let (p, i) = iter.next().unwrap();

        assert_eq!(p.0, i.0);
        assert_eq!(p.1.field1, i.1.field1);
        assert_eq!(p.1.field2, Some(i.1.field2));

        assert_eq!(partial.field4.field1, instance.field4.field1);
        assert_eq!(partial.field4.field2, Some(instance.field4.field2));
    }

    #[test]
    fn derive_struct_diff() {
        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField3 {
            #[partial(skip)]
            field1: String,
            field2: String,
        }

        let old = TestField3 {
            field1: "aaa".to_string(),
            field2: "bbb".to_string(),
        };

        let new = TestField3 {
            field1: "aaa".to_string(),
            field2: "ccc".to_string(),
        };

        let x = TestField3Partial::diff(&old, &new);
        assert_eq!(x.as_ref().unwrap().field1, "aaa");
        assert_eq!(x.unwrap().field2.unwrap(), "ccc");

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct Test {
            field1: String, // -> Option<String>

            #[partial(skip)]
            field2: String, // -> String

            #[partial(recursive)]
            field3: HashMap<i32, TestField3>, // ->  Option<HashMap<i32, TestField3Partial>>

            #[partial(skip, recursive)]
            field4: TestField3, // ->  TestField3Partial
        }

        let x1 = Test {
            field1: "aaa".to_string(),
            field2: "bbb".to_string(),
            field3: HashMap::from([(
                1_i32,
                TestField3 {
                    field1: "bbb".to_string(),
                    field2: "cccc".to_string(),
                },
            )]),
            field4: TestField3 {
                field1: "ccc".to_string(),
                field2: "ddd".to_string(),
            },
        };

        let x2 = Test {
            field1: "aaa".to_string(),
            field2: "bbb".to_string(),
            field3: HashMap::from([(
                1_i32,
                TestField3 {
                    field1: "bbb".to_string(),
                    field2: "dddd".to_string(),
                },
            )]),
            field4: TestField3 {
                field1: "ddd".to_string(),
                field2: "ddd".to_string(),
            },
        };

        let result = TestPartial::diff(&x1, &x2);
        assert!(result.as_ref().unwrap().field1.is_none());
        assert_eq!(result.as_ref().unwrap().field2, "bbb".to_string());
        assert_eq!(
            result.as_ref().unwrap().field3.clone().unwrap(),
            HashMap::from([(
                1,
                TestField3Partial {
                    field1: "bbb".to_string(),
                    field2: Some("dddd".to_string())
                }
            )])
        );
        assert_eq!(result.as_ref().unwrap().field4.field1, "ddd".to_string());
        assert!(result.as_ref().unwrap().field4.field2.is_none());

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct Test5 {
            #[partial(recursive)]
            field3: Vec<TestField3>, // ->  Option<Vec<TestField3Partial>>
        }

        let x1 = Test5 {
            field3: vec![TestField3 {
                field1: "aaa".to_string(),
                field2: "bbb".to_string(),
            }],
        };

        let x2 = Test5 {
            field3: vec![TestField3 {
                field1: "aaa".to_string(),
                field2: "vvv".to_string(),
            }],
        };

        let result = Test5Partial::diff(&x1, &x2);

        assert!(result.as_ref().unwrap().field3.is_some());

        let fields = result.as_ref().unwrap().field3.clone().unwrap();
        assert_eq!(fields[0].field1, "aaa".to_string());
        assert_eq!(fields[0].field2, Some("vvv".to_string()));
    }

    #[test]
    fn derive_struct_diff_more_items_in_hashmap() {
        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct HashMapValue {
            field1: String,
        }

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField {
            #[partial(recursive)]
            field: HashMap<String, HashMapValue>,
        }

        let t1 = TestField {
            field: HashMap::from([(
                "aaa".to_string(),
                HashMapValue {
                    field1: "Meee".to_string(),
                },
            )]),
        };

        let t2 = TestField {
            field: HashMap::from([
                (
                    "aaa".to_string(),
                    HashMapValue {
                        field1: "Meee".to_string(),
                    },
                ),
                (
                    "bbb".to_string(),
                    HashMapValue {
                        field1: "MeeToo".to_string(),
                    },
                ),
            ]),
        };

        let diff = TestFieldPartial::diff(&t1, &t2);

        assert!(diff.as_ref().unwrap().field.is_some());
        assert_eq!(diff.as_ref().unwrap().field.as_ref().unwrap().len(), 1);
        assert_eq!(
            diff.unwrap().field.unwrap().get("bbb").unwrap().field1,
            Some("MeeToo".to_string())
        );
    }

    #[test]
    fn derive_struct_diff_more_items_in_btreemap() {
        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct BTreeMapValue {
            field1: String,
        }

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField {
            #[partial(recursive)]
            field: BTreeMap<String, BTreeMapValue>,
        }

        let t1 = TestField {
            field: BTreeMap::from([(
                "aaa".to_string(),
                BTreeMapValue {
                    field1: "Meee".to_string(),
                },
            )]),
        };

        let t2 = TestField {
            field: BTreeMap::from([
                (
                    "aaa".to_string(),
                    BTreeMapValue {
                        field1: "Meee".to_string(),
                    },
                ),
                (
                    "bbb".to_string(),
                    BTreeMapValue {
                        field1: "MeeToo".to_string(),
                    },
                ),
            ]),
        };

        let diff = TestFieldPartial::diff(&t1, &t2);

        assert!(diff.as_ref().unwrap().field.is_some());
        assert_eq!(diff.as_ref().unwrap().field.as_ref().unwrap().len(), 1);
        assert_eq!(
            diff.unwrap().field.unwrap().get("bbb").unwrap().field1,
            Some("MeeToo".to_string())
        );
    }

    #[test]
    fn derive_struct_diff_exact_same_struct_no_changes() {
        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct HashMapValue {
            field1: String,
        }

        #[derive(Partial)]
        #[derive(PartialEq, Debug, Default, Clone)]
        struct TestField {
            #[partial(recursive)]
            field: HashMap<String, HashMapValue>,
        }

        let t1 = TestField {
            field: HashMap::from([(
                "aaa".to_string(),
                HashMapValue {
                    field1: "Meee".to_string(),
                },
            )]),
        };

        let t2 = TestField {
            field: HashMap::from([(
                "aaa".to_string(),
                HashMapValue {
                    field1: "Meee".to_string(),
                },
            )]),
        };
        let diff = TestFieldPartial::diff(&t1, &t2);

        assert!(diff.is_none());
    }

    #[test]
    fn derive_enum() {
        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct DataC {
            #[partial(skip)]
            id: usize,

            data: String,
        }

        #[derive(Partial)]
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Variant {
            // implicit skip
            A(String),

            // explicit skip
            B(#[partial(skip)] String),

            // implicit skip + recursive
            C(#[partial(recursive)] DataC),
        }

        let variant_a = Variant::A("a".to_string());
        let variant_b = Variant::B("b".to_string());
        let variant_c = Variant::C(DataC {
            id: 42,
            data: "foo".to_string(),
        });

        let variant_a_partial = variant_a.to_partial();
        let variant_b_partial = variant_b.to_partial();
        let variant_c_partial = variant_c.to_partial();

        // implicit skip must be applied
        assert_eq!(variant_a_partial, VariantPartial::A("a".to_string()));
        assert_eq!(variant_b_partial, VariantPartial::B("b".to_string()));
        assert_eq!(
            variant_c_partial,
            VariantPartial::C(DataCPartial {
                id: 42,
                data: Some("foo".to_string())
            })
        );
    }

    #[test]
    fn derive_enum_diff() {
        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct DataC {
            #[partial(skip)]
            id: usize,

            data: String,
        }

        #[derive(Partial)]
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Variant {
            // // implicit skip
            A(String),

            // explicit skip
            B(#[partial(skip)] String),

            // implicit skip + recursive
            C(#[partial(recursive)] DataC),
        }

        let variant_a = Variant::A("test".to_string());
        let variant_a_2 = Variant::A("test2".to_string());
        let variant_a_diff = VariantPartial::diff(&variant_a, &variant_a_2);

        let expected = "test2".to_string();
        assert!(matches!(variant_a_diff.unwrap(), VariantPartial::A(m) if expected == m));

        let variant_b = Variant::B("test3".to_string());
        let variant_b_2 = Variant::B("test4".to_string());
        let variant_b_diff = VariantPartial::diff(&variant_b, &variant_b_2);

        let expected = "test4".to_string();
        assert!(matches!(variant_b_diff.unwrap(), VariantPartial::B(m) if expected == m));

        let variant_c = Variant::C(DataC {
            id: 42,
            data: "foo".to_string(),
        });

        let variant_c_2 = Variant::C(DataC {
            id: 48,
            data: "foo".to_string(),
        });

        let variant_c_diff = VariantPartial::diff(&variant_c, &variant_c_2);

        let expected = DataCPartial { id: 48, data: None };
        assert!(matches!(variant_c_diff.unwrap(), VariantPartial::C(m) if expected == m));
    }

    #[test]
    fn derive_enum_diff_different_enum_variants() {
        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct DataC {
            #[partial(skip)]
            id: usize,

            data: String,
        }

        #[derive(Partial)]
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Variant {
            // // implicit skip
            A(String),

            // implicit skip + recursive
            C(#[partial(recursive)] DataC),
        }

        let variant_a = Variant::A("test".to_string());
        let variant_c = Variant::C(DataC {
            id: 48,
            data: "foo".to_string(),
        });

        let variant_diff = VariantPartial::diff(&variant_a, &variant_c);

        let expected = DataCPartial {
            id: 48,
            data: Some("foo".to_string()),
        };
        assert!(matches!(variant_diff.unwrap(), VariantPartial::C(m) if expected == m));
    }

    #[test]
    fn derive_enum_diff_exact_same_enum_no_changes() {
        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct DataC {
            #[partial(skip)]
            id: usize,

            data: String,
        }

        #[derive(Partial)]
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Variant {
            // implicit skip + recursive
            C(#[partial(recursive)] DataC),
        }

        let variant_c_old = Variant::C(DataC {
            id: 48,
            data: "foo".to_string(),
        });
        let variant_c_new = Variant::C(DataC {
            id: 48,
            data: "foo".to_string(),
        });

        let variant_diff = VariantPartial::diff(&variant_c_old, &variant_c_new);

        assert!(variant_diff.is_none());
    }

    #[test]
    fn symbols_with_generics() {
        trait Foo: PartialEq + Clone {}

        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct Data1<F: Foo> {
            id: usize,
            data: F,
        }

        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct Data2<F>
        where
            F: Foo,
        {
            id: usize,
            data: F,
        }

        #[derive(Partial)]
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum Data3<F: Foo> {
            Var1(F),
        }

        #[derive(Debug, Clone, PartialEq)]
        struct FooImpl;

        impl Foo for FooImpl {}

        let x = Data1 {
            id: 42,
            data: FooImpl,
        };

        let partial = x.into_partial();

        assert_eq!(partial.id, Some(42));
        assert_eq!(partial.data, Some(FooImpl));

        let x = Data2 {
            id: 42,
            data: FooImpl,
        };

        let partial = x.into_partial();

        assert_eq!(partial.id, Some(42));
        assert_eq!(partial.data, Some(FooImpl));

        let x = Data3::Var1(FooImpl);
        let partial = x.into_partial();

        assert!(matches!(partial, Data3Partial::Var1(FooImpl)));
    }

    #[test]
    fn optional_skip_recursive() {
        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct Data {
            #[partial(skip)]
            id: usize,

            #[partial(skip, rescursive)]
            inner: Option<DataInner>,
        }

        #[derive(Partial)]
        #[derive(Default, Debug, Clone, PartialEq, Eq)]
        struct DataInner {
            enabled: bool,
        }

        // none set
        let data_a = Data {
            id: 10,
            inner: None,
        };
        let data_b = Data {
            id: 10,
            inner: None,
        };
        let diff = DataPartial::diff(&data_a, &data_b);
        assert_eq!(diff, None);

        // only old set
        let data_a = Data {
            id: 10,
            inner: Some(DataInner { enabled: false }),
        };
        let data_b = Data {
            id: 10,
            inner: None,
        };
        let diff = DataPartial::diff(&data_a, &data_b);
        assert_eq!(diff.unwrap().inner, None);

        // only new set
        let data_a = Data {
            id: 10,
            inner: None,
        };
        let data_b = Data {
            id: 10,
            inner: Some(DataInner { enabled: false }),
        };
        let diff = DataPartial::diff(&data_a, &data_b);
        assert_eq!(diff.unwrap().inner.unwrap().enabled, false);

        // both set
        let data_a = Data {
            id: 10,
            inner: Some(DataInner { enabled: false }),
        };
        let data_b = Data {
            id: 10,
            inner: Some(DataInner { enabled: true }),
        };
        let diff = DataPartial::diff(&data_a, &data_b);
        assert_eq!(diff.unwrap().inner.unwrap().enabled, true);
    }
}
