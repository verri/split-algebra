import SplitAlgebra.Core.Ops

/-!
The classic leak: joining back a statistic computed from the whole table.

The composite `T ↦ innerJoin key T (g T)`, where the reference table `g T` depends on
all of `T`, is not split invariant even though `innerJoin` with a fixed right table is
split safe (`innerJoin_splitSafe`): the failure is inherited from `g`, whose reference is
not aligned with a split of `T`.  We take `g` to be the global mean of a numeric column
and mean imputation to be that join followed by a row-wise fill, and refute split
invariance of both on the table of the paper's opening figure (ages `20, ?, 40, 60`,
split into the first two and the last two rows).  Keys are `Fin 4`, so the figure's ids
`1..4` are `0..3` here.

Results:

- `joinMean_not_splitInvariant`: joining each row with the global mean.
- `imputeMean_not_splitInvariant`: mean imputation.
-/

namespace SplitAlgebra

variable {K : Type} [Fintype K]

/-- A table with one numeric column. -/
abbrev NumTable (K : Type) := Table K Unit (fun _ => ℚ)

/-- The present values of the column, gathered from every key. -/
def presentValues (T : NumTable K) : Multiset ℚ :=
  ∑ k, (T.rows k).filterMap (fun f => f ())

/-- The mean of the present values of the whole table. -/
def globalMean (T : NumTable K) : ℚ :=
  (presentValues T).sum / (presentValues T).card

/-- The reference table holding the global mean at its single key. -/
def meanRef (T : NumTable K) : NumTable Unit :=
  ⟨fun _ => {fun _ => some (globalMean T)}⟩

/-- Join each row with the global mean: `T ↦ innerJoin key T (g T)` with `g = meanRef`. -/
def joinMean (T : NumTable K) : Table K (Unit ⊕ Unit) (Sum.elim (fun _ => ℚ) (fun _ => ℚ)) :=
  innerJoin (fun _ => ()) T (meanRef T)

/-- Mean imputation: join with the global mean, then keep the value if present and the
mean otherwise. -/
def imputeMean (T : NumTable K) : NumTable K :=
  flatMap (fun _ f =>
    ({fun _ => (f (Sum.inl ()) : Option ℚ).or (f (Sum.inr ()))} :
      Multiset (Row Unit (fun _ => ℚ)))) (joinMean T)

private theorem filterMap_singleton {α β : Type _} (f : α → Option β) (a : α) :
    Multiset.filterMap f {a} = (f a).elim 0 (fun b => {b}) := by
  show Multiset.filterMap f (a ::ₘ 0) = _
  cases h : f a with
  | none => rw [Multiset.filterMap_cons_none _ _ h]; simp
  | some b => rw [Multiset.filterMap_cons_some _ _ _ h]; simp

/-- The table of the opening figure: ages `20, ?, 40, 60` at ids `0..3`. -/
def figTable : NumTable (Fin 4) :=
  ⟨![{fun _ => some 20}, {fun _ => none}, {fun _ => some 40}, {fun _ => some 60}]⟩

/-- The split of the opening figure: ids `0, 1` on one side, `2, 3` on the other. -/
def figSplit : Fin 4 → Bool := fun k => decide (2 ≤ k.val)

/-- Joining each row with a statistic of the whole table is not split invariant: at
id `0` the whole table joins the mean `40`, while its half joins the mean `20`. -/
theorem joinMean_not_splitInvariant : ¬ SplitInvariant (joinMean (K := Fin 4)) := by
  intro h
  have e := h _ _ (split_disjoint figSplit figTable)
  rw [union_split] at e
  have := congrArg (fun X => ((X.rows 0).map (fun f => (f (Sum.inr ()) : Option ℚ)))) e
  simp [joinMean, innerJoin, flatMap, union, split, meanRef, globalMean, presentValues,
    figTable, figSplit, Fin.sum_univ_four, filterMap_singleton] at this
  norm_num at this

/-- Mean imputation is not split invariant: the missing age at id `1` is imputed as
`40` from the whole table and as `20` from its half. -/
theorem imputeMean_not_splitInvariant : ¬ SplitInvariant (imputeMean (K := Fin 4)) := by
  intro h
  have e := h _ _ (split_disjoint figSplit figTable)
  rw [union_split] at e
  have := congrArg (fun X => ((X.rows 1).map (fun f => f ()))) e
  simp [imputeMean, joinMean, innerJoin, flatMap, union, split, meanRef, globalMean,
    presentValues, figTable, figSplit, Fin.sum_univ_four, filterMap_singleton] at this
  norm_num at this

end SplitAlgebra
