module

public import Gw444

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `Gw444.Defs`).

* `exists_good`: the explicit colourings `col4`, `col5`, `col6` of `Gw444.Colourings`, checked by
  `decide +kernel` through the Boolean test of `Gw444.Check`;
* `lt_of_gwProperty`, `lt_GW`: a good exact colouring of `[1, 328]` puts every threshold above `328`
  (`lt_of_good`, `lt_GW_of_good`);
* `exists_canonical`: the 4-colouring read as a colouring by natural numbers.
-/

namespace Gw444

theorem exists_good (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) :
    ∃ c : ℕ → Fin r, IsGoodExactColouring r 4 4 328 c := by
  rcases (by omega : r = 4 ∨ r = 5 ∨ r = 6) with rfl | rfl | rfl
  · exact ⟨col4, good4⟩
  · exact ⟨col5, good5⟩
  · exact ⟨col6, good6⟩

theorem lt_of_gwProperty (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) (M : ℕ) (hM : GWProperty r 4 4 M) :
    328 < M := by
  obtain ⟨c, hc⟩ := exists_good r h4 h6
  exact lt_of_good hc hM

theorem lt_GW (r : ℕ) (h4 : 4 ≤ r) (h6 : r ≤ 6) (hex : ∃ M, GWProperty r 4 4 M) :
    328 < GW r 4 4 := by
  obtain ⟨c, hc⟩ := exists_good r h4 h6
  exact lt_GW_of_good hc hex

theorem exists_canonical :
    ∃ c : ℕ → ℕ,
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 3 * d ≤ 328 →
        ¬ ∀ i < 4, ∀ j < 4, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 3 * d ≤ 328 → ¬ ∀ j < 4, c (x + j * d) = c x) := by
  obtain ⟨_, hrb, hmono⟩ := good4
  refine ⟨fun x => (col4 x : ℕ), ?_, ?_⟩
  · intro x d hx hd hxd hall
    exact hrb x d hx hd hxd fun i hi j hj hij h => hall i hi j hj hij (congrArg Fin.val h)
  · intro x d hx hd hxd hall
    exact hmono x d hx hd hxd fun j hj => Fin.ext (hall j hj)

end Gw444
