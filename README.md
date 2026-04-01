# lean-formalization

Formalizations of mathematical results in Lean 4.

## Desnanot-Jacobi Identity

The file `dj.lean` contains a proof of the Desnanot-Jacobi determinantal identity (also known as the Lewis Carroll / Dodgson condensation identity):

$$\det(M) \cdot \det(M^{1,k}_{1,k}) = \det(M^1_1) \cdot \det(M^k_k) - \det(M^1_k) \cdot \det(M^k_1)$$

where $M^i_j$ denotes the matrix with row $i$ and column $j$ deleted, and $M^{i,j}_{i,j}$ denotes the matrix with rows $i,j$ and columns $i,j$ deleted.

The proof constructs an auxiliary matrix using the adjugate and extracts the identity from the determinant of the product $M \cdot M'$, following the approach in Bressoud's *Proofs and Confirmations: The Story of the Alternating Sign Matrix Conjecture* (Cambridge University Press, 1999).

## Cauchy Determinant Formula

The file `cauchy.lean` proves that the determinant of the Cauchy matrix $C_{ij} = (x_i + y_j)^{-1}$ equals

$$\det(C) = \frac{\prod_{i < j} (x_i - x_j) \cdot \prod_{i < j}(y_i - y_j)}{\prod_{i,j}(x_i + y_j)}$$

The proof uses strong induction on $n$, with the Desnanot-Jacobi identity providing the inductive step. There are shorter proofs of the Cauchy determinant -- but this approach avoids row and column operations entirely and reduces the problem to verifying an algebraic identity on the closed-form product. All the determinant machinery is handled by Desnanot-Jacobi. The same strategy should work for any determinant with a nice closed product form.