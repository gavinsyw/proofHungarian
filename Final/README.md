# proofHungarian

Verification of Hungarian Algorithm using Coq

## Compilation

Some of our definitions rely on the coq files in graph/ and lib/ folders. Make them first. We have two files, one for definition and another for proving. Therefore, you should compile

> graph_definition.v

first and then compile the other v file named

> match.v

where all the problem statements and proofs are.

## Problem Statement

We mainly focus on proving the following three problems about Hungarian Algorithm:

> According to the Hungarian Algorithm, we can define a dfs process by small-step semantics, and then we can find an augment path by dfs.

> Given a match and an augment path, we can always establish a larger match, which is a match with greater cardinality than the original one.

> Given a match and a larger match, we can always find an augment path based on the original match. 

The first problem is the correctness of DFS search described in the Hungarian Algorithm, the second and third problem are summarized as Berge's Lemma, which is the base of generating maximum matching on augment paths.

## Proof Sketch

### DFS Search for Augment Path

We used small-step semantics to define the DFS process in searching a cross path. The DFS search starts with a given vertex, goes through unmatched edge and matched edge sequentially, and stops when it hits an unmatched vertex. If the search goes into a dead end, the DFS will go back to the last state and try another path.

After defining small-step semantics for DFS, we define the problem as:

> If the DFS starts at v and halts at a specific state, then the path at the halt state is an augment path.

The theorem is then proved in such a sequence:

1. The path at the halt state is a cross path.
2. The path at the halt state has a length of an odd number.
3. The path starts and stops at unmatched vertex.
4. The path is indeed an augment path.

### Augment Path to Larger Match

After getting an augment path from small step semantics, we need to prove that combining it and the current match will return a larger match. We prove the theorem in such a sequence:

1. Define the operation of "xor", i.e., symmetric difference, of list of edges.
2. The new edge list equals to : original match xor augment path, therefore the new edge list is a match.
3. The augment path has one more unmatched edges than the matched edges.
4. The length of the new edge list is larger than the original match by one.
5. The new edge list is a larger match than the original one.

### Larger Match to Augment Path

There are some difficulties in proving larger match to augment path. The intuition is to do induction on the larger match. Some lemmas in this part have not been proved, but they appear to be right. We prove the theorem in such a sequence:

1. Define the concept of a match with no repeating edges. Our definition of a match is undirected. Therefore, two edges of the opposite direction appears at the same time in a match. However, when we need to prove the augment path, we only need a directed match. Therefore, we define a match with no repeating edges as nod, and the operation that transforms a match into a nod as to_nod.
2. Prove that from a larger match, which only differs from the original match by one edge, we can generate an augment path.
3. Prove that from a match, we can always generate a smaller match which only differs from the original match by one edge. (This proof is not completed)
4. Prove that from a larger match we can always generate an augmenting path based on the original match.
