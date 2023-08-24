use proc_macro_crate::FoundCrate;
use quote::format_ident;
use quote::quote;

use syn::*;

mod partial;

/// Partial macro creates new struct or enum out of existing and it makes its fields optional.
/// Macro MUST be in separate derive above other derives
///
/// Macro supports two attributes:
///
/// `#[partial(skip)]` - this will leave field(variable) as it is, will not apply Option<X>
///
/// `#[partial(recursive)]` - This will change type from `Foo` to `<Foo as IntoPartial>::Partial` if
/// `Foo` implements `IntoPartial`.
///
/// Those two attributes can be combined
///
/// `#[partial(skip, recursive)]` - this will not apply option but field will be partial
///
/// Examples:
///
/// INPUT:
///
/// ```rust
/// # use partial_rs::Partial;
/// use serde::Serialize;
///
/// use std::collections::HashMap;
///
/// #[derive(Partial)]
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct AnotherNested {
///     pub id: i32,
/// }
///
/// #[derive(Partial)]
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct Nested {
///     pub aaa: String,
///     pub hashmap: HashMap<String, String>,
///     #[partial(recursive)]
///     pub hashmap2: HashMap<String, AnotherNested>
/// }
///
/// #[derive(Partial)]
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct Test {
///    #[serde(rename="test")]
///     pub aaa: String,
///     #[partial(recursive)]
///     pub bbb: Nested,
///     #[partial(skip, recursive)]
///     pub ccc: Nested,
///
/// }
/// ```
///
/// OUTPUT:
///
/// ```rust
/// # use partial_rs::Partial;
/// use serde::Serialize;
///
/// use std::collections::HashMap;
///
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct AnotherNestedPartial {
///     pub id: Option<i32>,
/// }
///
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct NestedPartial {
///     pub aaa: Option<String>,
///     pub hashmap: Option<HashMap<String, String>>,
///     pub hashmap2: Option<HashMap<String, AnotherNestedPartial>>,
/// }
///
/// #[derive(Debug, PartialEq, Serialize, Clone)]
/// pub struct TestPartial {
///     #[serde(rename = "test")]
///     pub aaa: Option<String>,
///     pub bbb: Option<NestedPartial>,
///     pub ccc: NestedPartial,
/// }
/// ```
#[proc_macro_derive(Partial, attributes(partial))]
pub fn partial(tokens_input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let krate = crate_name();

    let DeriveInput {
        attrs,
        vis,
        ident,
        data,
        generics,
    } = syn::parse(tokens_input).expect("No DeriveInput");

    let orig_ident = ident.clone();
    let ident = format_ident!("{ident}Partial");

    match data {
        Data::Struct(data) => {
            partial::to_struct(krate, vis, attrs, orig_ident, ident, data, generics)
        }
        Data::Enum(data) => partial::to_enum(krate, vis, attrs, orig_ident, ident, data, generics),
        _ => panic!("expected a named struct or unnamed enum"),
    }
}

fn crate_name() -> proc_macro2::TokenStream {
    let found_crate = proc_macro_crate::crate_name("partial-rs")
        .expect("partial-rs must be present in Cargo.toml");

    match found_crate {
        FoundCrate::Itself => quote!(crate),
        FoundCrate::Name(name) => {
            let ident = Ident::new(&name, proc_macro2::Span::call_site());
            quote!( #ident )
        }
    }
}
