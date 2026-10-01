/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SpecifiedLieCloning

/-! The fixed concrete Cartan channels on specified highest-weight models.
Their definitions depend only on the representations, not on a spectrum,
a depth cutoff, an error bound, or an orbit parameter. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open CartanChannel CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Nonempty A] [Nonempty B] [Nonempty C]

def specifiedForward (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) : Channels.MatrixChannel A C :=
  cartanChannel (specifiedCartanEmbedding M N S hrow)
    (Fintype.card A) (Fintype.card C) (by exact_mod_cast Fintype.card_pos)
    (by exact_mod_cast Fintype.card_pos)
    (CartanBalance.balance_of_cyclic_weight M N S _
      (specifiedCartanEmbedding_isometry M N S hrow)
      (specifiedCartanEmbedding_intertwines M N S hrow))

def specifiedReverse (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) : Channels.MatrixChannel C A :=
  reverseChannel (specifiedCartanEmbedding M N S hrow)
    (specifiedCartanEmbedding_isometry M N S hrow)

end FreeEntropy.CartanLieCloning
