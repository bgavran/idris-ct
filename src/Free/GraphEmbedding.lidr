\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
\fi

> module Free.GraphEmbedding
>
> import Data.Fin
> import Data.Vect
> import Control.Isomorphism
> import Basic.Category
> import Free.FreeFunctor
> import Free.Graph
>
> %access public export
> %default total
> 
> 
> -- the type of morphisms
> mor' : Category -> Type
> mor' cat = (a : obj cat ** b : obj cat ** mor cat a b)


Assuming G graph fixed and target category cat fixed
Assuming vertices is enumerated and ordered:
([A,B,C,...], [f:A \to B, g:B \to C, ...])
This couple is legal if:
- Elements of the first list are objects of cat
- Elements of the second list are morphisms of cat 
- The length of the first list is the same as the number of vertices in G
- The length of the second list is the same as the number of edges in G
-  For each element j of the second list:
-- make sure that MapObj(source(edge_j) ) = source element j
--- Suppose edge_j is sent to f:A -> B
--- Suppose source(edge_j) is vertex_i
--- Then I want i-th position in the first list to be (syntactically) equal to A. 

-- make sure that MapObj(target(edge_j) ) = target element j

> aux : {to : gv -> Fin k} -> Edge (MkGraph gv ne ge) i j -> (v : Vect k (obj cat)) -> (e : Vect (numEdges g) (mor' cat)) -> mor cat (Vect.index (to i) v) (Vect.index (to j) v)
> aux {to} {ge=(i,j)::ge} Here v e with (index (to i) v) 
>   aux {to} {ge=(i,j)::ge} Here v e | vi with (index (to j) v) 
>     aux {to} {ge=(i,j)::ge} Here v e | vi | vj = ?wat 
        
         let l be the current position in the list (where `Here` is). We can get l as the length of ge I think
         Then compare vi with the source of `index l e` and vj with the target of `index l e`
         ie, cast `index l e` to the type `mor cat vi vj`, which might not be possible, thus we need the `Maybe` type
         so, we case split on `index l e`, which gives us two objects, a and b and a morphism a -> b
         then use decidable equality on a == vi, b == vj, and if those are equal, return Just ..., otherwise Nothing

> aux (There el) v e = ?wat2

 graphEmbedding : Iso (vertices g) (Fin k) -> Vect k (obj cat) -> Vect (numEdges g) (mor' cat) -> Maybe (GraphEmbedding g cat)
 graphEmbedding {cat} {g=MkGraph gv ne ge} (MkIso to from tf ft) v e = 
   Just $ MkGraphEmbedding (flip index v . to) aux


[v1 v2]
[e: v2 -> v1]

([B, A],[f:B->A])

f

. -e> .   ====> A -f-> B

|
v
A











{-

> aux' : {to : gv -> Fin k} -> Edge (MkGraph gv ne ge) i j -> (v : Vect k (obj cat)) -> (obj cat)
> aux' {to} {ge=(i,j)::ge} Here v e with (index (to i) v) 
> aux' (There el) v e = ?wat6


-}