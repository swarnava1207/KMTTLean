# KMTTLean
In this repo I have tried to implement Kirchoff's Matrix Tree Theorem. \
The theorem states that the number of spanning trees in any graph is equal to the determinant of its reduced Laplacian Matrix.
## Module Docs
The module docs for this library is [here](https://swarnava1207.github.io/KMTTLean/doc/)
## Brief Implementation Details
- **Graph.lean** - This file has the definitions related to SimpleGraphs and Spanning Trees, including the structure of spanning trees and a set enumerating all the spanning trees of the Graph.
- **Matrices.lean** - This file contains definitions related to matrices of SimpleGraphs. It also gives an alternate definition of Edges of a SimpleGraph.
- **Theorem.lean** - This file contains the three main lemmas and other lemmas needed to prove these three. These three lemmas are mainly used to prove the original theorem
- **Main.lean** - This file contains the main theorem, Kirchoff's Matrix Tree Theorem
- **Stuff.lean** - This file contains definitions and some theorems that I first used, but later left for something easier. 

