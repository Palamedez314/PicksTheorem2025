# Pick's Theorem in Lean

This is our take at formalizing Pick's theorem in Lean 4, 
developed by a student working group at the University of Stuttgart.
As our core result we formalize Pick's lemma, as explained in the article 
[Formalizing Pick's Theorem, efficiently](https://github.com/Palamedez314/PicksTheorem2025/blob/main/PicksTheorem2025/Article/Pick-in-Lean.pdf). 

![polygons](https://github.com/Palamedez314/PicksTheorem2025/blob/main/PicksTheorem2025/Article/Polygons-and-Pick.jpg)

## From Pick's lemma to Pick's theorem

So far we have focused on Pick's lemma as our central contribution.
Two more classical theorems complete the picture:
First, we need Jordan's decomposition to formulate Pick's theorem precisely,
translating it from geometric to algebraic terms.
Second, we add Hopf's umlaufsatz to interpret the counting result
in a more geometric and user-friendly fashion.

![lemma to theorem](https://github.com/Palamedez314/PicksTheorem2025/blob/main/PicksTheorem2025/Article/Pick-lemma-to-theorem.jpg)
