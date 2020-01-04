# Module Names

Follow the standard library conventions by and large, i.e. a top-level module
like Data.List, which imports Data.List.Base.
If the module is small enough to just fit in the top-level, then just have one
module. 

For common sub-modules, the following names should be used:

- Literals: list, string, character, or number syntax.
- Properties
- Relation.Unary/Binary/etc.
- Sugar: Applicative and monadic operators for sugar

# Eliminators

