# Quick Summary

- Torsor over vector space == affine space
- Points are represented by tuples of rational
- Vectors are represented by tuples of rationals
- Scalars are represented by rationals

We've provided you with a template for progress.

We've already required that K is (and scalars come 
from) a field. Unless you have another idea (that'd 
be fine but talk to me about it) you should proceed 
to define typeclass instances to augment AffVector 
with the structure of an additive commutative group,
part of the way to defining it as a vector space,
which is what we need the actions to be to have an
affine space. 

Hint: Follow the pattern we used previously to 
establish that the symmetries of an equilateral 
triangle form a torsor over a group of rotations.