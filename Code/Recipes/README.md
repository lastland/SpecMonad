`DMRecipe.v` contains the base recipe that one can use to define a `DijkstraMoand.v`.
`Logic.v` needs an instance of `DMRecipe.v` + ....

On top of a Logic, one can create a triple using ApproxGC that takes
an extra `W'` that is expected to be in a Galois connection with `W`
for a direction.
