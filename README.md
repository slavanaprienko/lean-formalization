# lean-formalization

Formalizations of mathematical results in Lean 4.

## Desnanot-Jacobi Identity

The file `dj.lean` contains a proof of the Desnanot-Jacobi determinantal identity (also known as the Lewis Carroll / Dodgson condensation identity):

$$\det(M) \cdot \det(M^{1,k}_{1,k}) = \det(M^1_1) \cdot \det(M^k_k) - \det(M^1_k) \cdot \det(M^k_1)$$

where $M^i_j$ denotes the matrix with row $i$ and column $j$ deleted, and $M^{i,j}_{i,j}$ denotes the matrix with rows $i,j$ and columns $i,j$ deleted.

The proof constructs an auxiliary matrix using the adjugate and extracts the identity from the determinant of the product $M \cdot M'$, following the approach in Bressoud's *Proofs and Confirmations: The Story of the Alternating Sign Matrix Conjecture* (Cambridge University Press, 1999).