# Hypergraph
Utilities for cospans, wiring diagrams, frobenius algebras and spans along with more basic utilities for morphisms in (symmetric) monoidal categories and flavors of FinSet

[Fong-Spivak Hypergraph Categories](https://arxiv.org/pdf/1806.08304.pdf)

[Span and Cospan](https://en.wikipedia.org/wiki/Span_(category_theory))

## Cospan

The notion of cospan here is for finite sets sliced over some Lambda.
So the domain and codomain are sets equipped with a map to Lambda.
The middle finite set is also such a set and there are left and right maps coming from the domain/codomain respectively.
The lambda labels on all must line up for those maps.
The type called Cospan here is for the morphisms in this category.
Use Lambda = () to avoid the extra baggage of Cospan_\Lambda vs the usual Cospan category.

In order to make adding, removing and changing the domain/codomain easier, there is a NamedCospan which names all of the elements in the boundary sets.
Then one can delete and change the maps based on these names.

## Wiring Diagrams

This operad is built on top of Cospans.

### TODO : draw a picture

## Span/Rel

Again over Lambda  which can be taken to be () for a first pass.

## Frobenius

Encode morphisms built from the 4 distinguished morphisms of a Frobenius object, the braiding and allow black boxes for any other morphism.
These black boxes are labelled with some BlackBoxLabel and one must provide a function that takes that label and the domain/codomain to some
type T which represents the morphisms in a symmetric monoidal category where each object labelled by Lambda has been given the structure of a Frobenius object.
The more general objects are presented as tensor products of these basic objects.

## Brauer

[Brauer Algebra](https://en.wikipedia.org/wiki/Brauer_algebra)

## Category Traits

There are traits which when implemented indicate that is a morphism in some category. That category can also be monoidal and symmetric monoidal. For example,
if one implements the trait to say T indicates a morphism in a monoidal category, then we have functions which give the identity morphisms on specified objects,
compose T's to another (there are two versions of this for whether this is done by mutating one of the inputs or producing a fresh T). Because the category
is not symmetric monoidal in this case, there isn't the trait that provides the functions for producing and manipulating morphisms from Permuatations.

Similar to Frobenius we can interpret a generic monoidal morphism in any such trait. The generic monoidal morphism encodes how to build up a morphism from
some BlackBox, monoidal product and composition. Suppose T implements all the traits needed to be a morphism in a monoidal category. Then if one
also gives a function that takes that BlackBox label and the domain/codomain then the interpret function produces the corresponding T using the functions of the
monoidal and composition traits.
