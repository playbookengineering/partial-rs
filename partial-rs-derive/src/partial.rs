use proc_macro2::{TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::*;

use syn::parse::ParseStream;
use syn::{punctuated::Punctuated, token::Comma};

const PARTIAL: &str = "partial";
const PARTIAL_OPERATION_SKIP: &str = "skip";
const PARTIAL_OPERATION_RECURSIVE: &str = "recursive";

#[derive(PartialEq, Eq, Clone, Copy)]
enum CodegenMode {
    Struct,
    Enum,
}

/// Creates struct which has all fields optional (unless skipped)
pub(crate) fn to_struct(
    krate: TokenStream,
    vis: Visibility,
    attrs: Vec<Attribute>,
    orig_ident: Ident,
    ident: Ident,
    struct_data: DataStruct,
    generics: Generics,
) -> proc_macro::TokenStream {
    let fields = match struct_data.fields {
        Fields::Named(f) => f.named,
        _ => panic!("Only named fields are supported right now"),
    };

    let f = parse_struct_fields(fields);
    let fields_decl = f.iter().map(|f| f.to_type(&krate, CodegenMode::Struct));
    let convs = f.iter().map(|f| {
        let ident = f.field.ident.as_ref().expect("Expected ident");
        let expr = f.to_conversion_expr(&krate, quote!(self.#ident));

        quote! {
            #ident: #expr
        }
    });

    // FIXME #[derive(Partial)] must be above other derives
    let derive = TokenStream::from_iter(attrs.into_iter().map(|x| x.to_token_stream()));

    let diffed_fields = f.iter().map(|f| {
        let ident = &f.field.ident;
        let diff = f.to_diff(
            &krate,
            CodegenMode::Struct,
            format_ident!("old"),
            format_ident!("new"),
        );

        quote! {
            #ident: #diff,
        }
    });

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let generated = quote! {
        #derive
        #vis struct #ident #generics {#(
            #fields_decl,
        )*}

        impl #impl_generics #krate::Diff for #ident #ty_generics #where_clause {
            type Orig = #orig_ident #ty_generics;

            fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
                use #krate::ToPartial as _;

                if old == new {
                    return None
                }

                Some(#ident {
                    #(
                        #diffed_fields
                    )*
                })
            }
        }

        impl #impl_generics #krate::IntoPartial for #orig_ident #ty_generics #where_clause {
            type Partial = #ident #ty_generics;

            fn into_partial(self) -> Self::Partial {
                use #krate::IntoPartial as _;

                Self::Partial {#(
                    #convs,
                )*}
            }
        }
    };

    proc_macro::TokenStream::from(generated)
}

pub fn to_enum(
    krate: TokenStream,
    vis: Visibility,
    attrs: Vec<Attribute>,
    orig_ident: Ident,
    ident: Ident,
    data: DataEnum,
    generics: Generics,
) -> proc_macro::TokenStream {
    let parsed_variants = parse_variants(data.variants);

    let variants = parsed_variants.iter().map(|variant| {
        let types = variant
            .fields
            .iter()
            .map(|f| f.to_type(&krate, CodegenMode::Enum));

        let ident = &variant.ident;

        quote! {
            #ident (#(#types, )*)
        }
    });

    let variant_idents = parsed_variants.iter().map(|variant| &variant.ident);

    let letters = ('a'..='z').map(|letter| format_ident!("{letter}"));

    let convs = parsed_variants
        .iter()
        .zip(letters.clone())
        .map(|(variant, letter)| {
            let convs = variant
                .fields
                .iter()
                .map(|f| f.to_conversion_expr(&krate, quote!(#letter)));

            quote! {
                #( #convs, )*
            }
        });

    let diffed_variants = parsed_variants.iter().zip(letters.clone()).zip(variant_idents.clone()).map(|((variant, letter), variant_ident)| {
        let o_ident = format_ident!("o_{letter}");
        let n_ident = format_ident!("n_{letter}");

        let types = variant
            .fields
            .iter()
            .map(|f| f.to_diff(&krate, CodegenMode::Enum, o_ident.clone(), n_ident.clone()));

        let convs = variant.fields.iter().map(|f| match f.operation {
            Operation::Optional | Operation::OptionalRecursive => {
                panic!("Optional & OptionalRecursive are not supported in enums!")
            },
            Operation::Skip => {
                quote!{#n_ident.clone()}
            },
            Operation::SkipRecursive => {
                quote!{#n_ident.to_partial()}
            },
        });

        quote! {
            #(
                (Self::Orig::#variant_ident(#o_ident), Self::Orig::#variant_ident(#n_ident)) => #ident::#variant_ident(#types),
                (_, Self::Orig::#variant_ident(#n_ident)) => #ident::#variant_ident(#convs)
            )*
        }
    });

    let derive = TokenStream::from_iter(attrs.into_iter().map(|a| a.into_token_stream()));

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let generated = quote! {
        #derive
        #vis enum #ident #generics {#(
            #variants,
        )*}

        impl #impl_generics #krate::Diff for #ident #ty_generics #where_clause {
            type Orig = #orig_ident #ty_generics;

            fn diff(old: &Self::Orig, new: &Self::Orig) -> Option<Self> {
                use #krate::ToPartial as _;

                if old == new {
                    return None
                }

                Some(match (old, new) {
                    #(
                        #diffed_variants,
                    )*
                })
            }
        }

        impl #impl_generics #krate::IntoPartial for #orig_ident #ty_generics #where_clause {
            type Partial = #ident #ty_generics;

            fn into_partial(self) -> Self::Partial {
                match self {#(
                    Self::#variant_idents(#letters) => Self::Partial::#variant_idents(#convs),
                )*}
            }
        }
    };

    proc_macro::TokenStream::from(generated)
}

/// Represents single type declaration
struct DataField {
    pub field: Field,
    pub attrs: proc_macro2::TokenStream,
    pub operation: Operation,
}

impl DataField {
    /// Constructs new type declaration
    ///
    /// struct FooPartial {
    ///   a: <quote here>,
    ///   b: <quote here>,
    ///
    ///   ...
    /// }
    ///
    /// enum FooPartial {
    ///   A(<quote here>),
    ///   B(<quote here>),
    ///
    ///   ...
    /// }
    fn to_type(&self, krate: &TokenStream, codegen_mode: CodegenMode) -> TokenStream {
        let ty = &self.field.ty;
        let vis = &self.field.vis;
        let attrs = &self.attrs;

        let ty = match self.operation {
            Operation::Optional => quote! {
                Option<#ty>
            },
            Operation::OptionalRecursive => quote! {
                Option<<#krate::Recursive<#ty> as #krate::IntoPartial>::Partial>

            },
            Operation::Skip => quote! {
                #ty
            },
            Operation::SkipRecursive => quote! {
                <#krate::Recursive<#ty> as #krate::IntoPartial>::Partial
            },
        };

        if codegen_mode == CodegenMode::Struct {
            let ident = self.field.ident.as_ref().expect("expected named type");

            quote! {
                #attrs #vis #ident: #ty
            }
        } else {
            quote! {
                #attrs #vis #ty
            }
        }
    }

    /// Constructs field/variant compartions
    fn to_diff(
        &self,
        krate: &TokenStream,
        codegen_mode: CodegenMode,
        old: Ident,
        new: Ident,
    ) -> TokenStream {
        let ident = &self.field.ident;
        let ty = &self.field.ty;

        let diffed = match codegen_mode {
            CodegenMode::Struct => match self.operation {
                Operation::Optional => quote! {
                    (old.#ident != new.#ident).then(|| {
                        new.#ident.to_owned()
                    })
                },
                Operation::OptionalRecursive => quote! {
                    <#krate::Recursive<#ty> as
                        #krate::IntoPartial>::Partial::diff(&old.#ident, &new.#ident)

                },
                Operation::Skip => quote! {
                    (old.#ident != new.#ident).then(|| {
                        new.#ident.to_owned()
                    }).unwrap_or(new.#ident.to_owned())
                },
                Operation::SkipRecursive => quote! {
                    <#krate::Recursive<#ty> as
                        #krate::IntoPartial>::Partial::diff(&old.#ident, &new.#ident).unwrap_or(#new.#ident.to_partial())
                },
            },
            CodegenMode::Enum => match self.operation {
                Operation::Optional | Operation::OptionalRecursive => {
                    panic!("Optional & OptionalRecursive are not supported in enums!")
                }
                Operation::Skip => quote! {
                   (#old != #new).then(|| {#new.to_owned()}).unwrap_or(#new.to_owned())
                },
                Operation::SkipRecursive => quote! {
                    <#krate::Recursive<#ty> as
                        #krate::IntoPartial>::Partial::diff(&#old, &#new).unwrap_or(#new.to_partial())
                },
            },
        };

        quote! {
            #diffed
        }
    }

    /// Constructs conversion expression that converts complete to partial
    ///
    /// impl IntoPartial for Foo {
    ///   type Partial = FooPartial;
    ///
    ///   fn into_partial(self) -> Self::Partial {
    ///     Self::Partial {
    ///       a: <quote here>,
    ///       b: <quote here>,
    ///     }
    ///   }
    /// }
    fn to_conversion_expr(&self, krate: &TokenStream, tt: TokenStream) -> TokenStream {
        match self.operation {
            Operation::Optional => quote! {
                ::core::option::Option::Some(#tt)
            },
            Operation::OptionalRecursive => quote! {
                ::core::option::Option::Some(#krate::Recursive(#tt).into_partial())
            },
            Operation::Skip => quote! {
                #tt
            },
            Operation::SkipRecursive => quote! {
                #krate::Recursive(#tt).into_partial()
            },
        }
    }
}

enum Operation {
    Optional,
    OptionalRecursive,
    Skip,
    SkipRecursive,
}

fn parse_partial_attrs(attrs: &[&Attribute], codegen_mode: CodegenMode) -> Operation {
    let mut skip = false;
    let mut recursive = false;

    for attr in attrs {
        let _ = attr.parse_args_with(|input: ParseStream<'_>| {
            while let Some(token) = input.parse()? {
                if let TokenTree::Ident(ident) = token {
                    skip |= ident == PARTIAL_OPERATION_SKIP;
                    recursive |= ident == PARTIAL_OPERATION_RECURSIVE;
                }
            }
            Ok(())
        });
    }

    // always apply skip on enums
    //
    // #[derive(Partial)]
    // enum Variant {
    //   A(#[partial(recursive)] DataA),
    //   B(#[partial(recursive)] DataB)
    // }
    //
    // results in
    //
    // enum VariantPartial {
    //   Variant::A(DataAPartial),
    //   Variant::B(DataBPartial),
    // }
    //
    skip = skip || codegen_mode == CodegenMode::Enum;

    match (skip, recursive) {
        (true, true) => Operation::SkipRecursive,
        (true, false) => Operation::Skip,
        (false, true) => Operation::OptionalRecursive,
        (false, false) => Operation::Optional,
    }
}

/// Returns all struct fields that are divided into two groups, those that we need to apply Option and skipped which do not
fn parse_struct_fields(fields: Punctuated<Field, Comma>) -> Vec<DataField> {
    let mut ret = Vec::with_capacity(fields.len());

    for field in fields.into_iter() {
        let (partial_attrs, other_attrs): (Vec<_>, Vec<_>) = field
            .attrs
            .iter()
            .partition(|attr| attr.path.is_ident(PARTIAL));

        let other_attrs = quote! {
            #(
                #other_attrs
            )*
        };

        let operation = parse_partial_attrs(&partial_attrs, CodegenMode::Struct);

        ret.push(DataField {
            field: field.clone(),
            attrs: other_attrs,
            operation,
        });
    }

    ret
}

struct EnumVariant {
    ident: Ident,
    fields: Vec<DataField>,
}

fn parse_variants(variants: Punctuated<Variant, Comma>) -> Vec<EnumVariant> {
    let mut ret = Vec::with_capacity(variants.len());

    for variant in variants {
        let ident = variant.ident;
        let fields = match variant.fields {
            Fields::Unnamed(n) => n.unnamed,
            _ => panic!("Only unnamed enums are supported right now"),
        };

        let mut variant_fields = Vec::with_capacity(fields.len());

        for field in fields.into_iter() {
            let (partial_attrs, other_attrs): (Vec<_>, Vec<_>) = field
                .attrs
                .iter()
                .partition(|attr| attr.path.is_ident(PARTIAL));

            let other_attrs = quote! {
                #(
                    #other_attrs
                )*
            };

            let operation = parse_partial_attrs(&partial_attrs, CodegenMode::Enum);

            variant_fields.push(DataField {
                field,
                attrs: other_attrs,
                operation,
            })
        }

        ret.push(EnumVariant {
            ident,
            fields: variant_fields,
        });
    }

    ret
}
