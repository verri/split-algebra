/-
Split-safety of the operations: every operation of `SplitAlgebra.Core.Ops` except
`demote` is `SplitSafe`, hence composes into pipelines that stay
split-invariant.  `aggregate` separates `SplitInvariant` from `UnionHom`
(split-invariant, not a hom); `demote` separates `SplitInvariant` from
`SplitSafe` (a hom, hence split-invariant, yet not disjointness-preserving,
so unsafe to pipeline).

Main Source:  Chapter 5, section "Split-invariant operations", of
F. A. N. Verri (2026). Data Science Project: An Inductive Learning Approach.
Version v1.0.0. Victoria, British Columbia, Canada: Leanpub. doi:
10.5281/zenodo.18815798. url: https://leanpub.com/dsp.
-/

import SplitAlgebra.Core.Ops

namespace SplitAlgebra

variable {K H : Type _} {σ : H → Type}
variable {K' H' : Type _} {σ' : H' → Type}
variable {U G : Type _} {τ : G → Type}
variable {D : Type _}

/-- `flatMap` is a union-homomorphism, since `Multiset.bind` distributes over union. -/
theorem flatMap_unionHom (φ : K → Row H σ → Multiset (Row H' σ')) :
    UnionHom (flatMap φ) := by
  intro T₀ T₁
  apply Table.ext_rows
  intro k
  simp only [flatMap, union]
  exact Multiset.add_bind _ _ _

/-- Hence `flatMap` is split-invariant, the property SplitAlgebra enforces. -/
theorem flatMap_splitInvariant (φ : K → Row H σ → Multiset (Row H' σ')) :
    SplitInvariant (flatMap φ) := (flatMap_unionHom φ).splitInvariant

/-- `leftJoin` against a fixed table is a union-homomorphism: it is a `flatMap`. -/
theorem leftJoin_unionHom (key : K → U) (right : Table U G τ) :
    UnionHom (fun T => leftJoin (σ := σ) key T right) := by
  intro T₀ T₁
  apply Table.ext_rows
  intro k
  simp only [leftJoin, flatMap, union]
  exact Multiset.add_bind _ _ _

/-- Hence `leftJoin` is split-invariant. -/
theorem leftJoin_splitInvariant (key : K → U) (right : Table U G τ) :
    SplitInvariant (fun T => leftJoin (σ := σ) key T right) :=
  (leftJoin_unionHom key right).splitInvariant

/-- The unary, fixed-right `innerJoin` is a union-homomorphism: it is a `flatMap`. -/
theorem innerJoin_unionHom (key : K → U) (right : Table U G τ) :
    UnionHom (fun T => innerJoin (σ := σ) key T right) := by
  intro T₀ T₁
  apply Table.ext_rows
  intro k
  simp only [innerJoin, flatMap, union]
  exact Multiset.add_bind _ _ _

/-- Hence the unary, fixed-right `innerJoin` is split-invariant. -/
theorem innerJoin_splitInvariant (key : K → U) (right : Table U G τ) :
    SplitInvariant (fun T => innerJoin (σ := σ) key T right) :=
  (innerJoin_unionHom key right).splitInvariant

/-- `promote` is a union-homomorphism.  Each output key `(k, v)` reads only from
input key `k`, where the operation is `Multiset.bind`, which distributes over `+`. -/
theorem promote_unionHom {β : Type} [DecidableEq β] :
    UnionHom (promote (K := K) (H := H) (σ := σ) (β := β)) := by
  intro T₀ T₁
  apply Table.ext_rows
  rintro ⟨k, v⟩
  simp only [promote, union]
  exact Multiset.add_bind _ _ _

/-- Hence `promote` is split-invariant. -/
theorem promote_splitInvariant {β : Type} [DecidableEq β] :
    SplitInvariant (promote (K := K) (H := H) (σ := σ) (β := β)) :=
  promote_unionHom.splitInvariant

/-- `aggregate` *is* split-invariant -- the property SplitAlgebra enforces, and the
book's claim.  Under disjointness, at every key one summand is empty, so folding
the union is the same as folding the nonempty side. -/
theorem aggregate_splitInvariant (f : K → Multiset (Row H σ) → Row H σ) :
    SplitInvariant (aggregate f) := by
  intro T₀ T₁ hdisj
  apply Table.ext_rows
  intro k
  simp only [aggregate, union]
  rcases hdisj k with h | h
  · rw [h, zero_add]; simp
  · rw [h, add_zero]; simp

/-- `aggregate` is *not* a union-homomorphism: on a key present in both summands
it folds the merged bag to one row on the left but binds two aggregated rows on
the right.  This is the operation that separates `SplitInvariant` from the
strictly stronger `UnionHom`. -/
theorem aggregate_not_unionHom :
    ¬ UnionHom
        (aggregate (fun (_ : Unit) (_ : Multiset (Row Unit (fun _ => Unit))) =>
          fun _ => none)) := by
  intro h
  have hT := h ⟨fun _ => {fun _ => none}⟩ ⟨fun _ => {fun _ => none}⟩
  apply_fun (fun U => (U.rows ()).card) at hT
  simp [aggregate, union] at hT

/-- `demote` *is* a union-homomorphism (hence split-invariant): it sums each
dropped key's mapped rows, and both `Multiset.map` and `Finset.sum` distribute
over `+`.  So by the bare equation alone, `demote` looks safe. -/
theorem demote_unionHom [Fintype D] :
    UnionHom (demote (K := K) (H := H) (σ := σ) (D := D)) := by
  intro T₀ T₁
  apply Table.ext_rows
  intro k
  simp only [demote, union, Multiset.map_add]
  rw [Finset.sum_add_distrib]

/-- ...yet `demote` does *not* preserve disjointness, so it is **not**
`SplitSafe`.  Counterexample: two single-row tables that a split separates by the
dropped key (`d = false` vs `d = true`) both land on the same output key once
`d` is dropped.  This is precisely why a pipeline through `demote` -- e.g.
`aggregate ∘ demote`, the averaging case -- can disagree with the full-table
result: `aggregate` is then handed overlapping tables its guarantee does not
cover. -/
theorem demote_not_preservesDisjoint :
    ¬ PreservesDisjoint
        (demote (K := Unit) (σ := fun (_ : Unit) => Unit) (D := Bool)) := by
  intro h
  have hd := h
    ⟨fun p => if p.2 then 0 else {fun _ => none}⟩
    ⟨fun p => if p.2 then {fun _ => none} else 0⟩
    (by intro p; cases hp : p.2 <;> simp [hp]) ()
  simp [demote] at hd

/-! ### Split-safety of the operations

Every operation defined above preserves disjointness, hence is `SplitSafe`, hence
can be freely composed into pipelines that stay split-invariant.  Each acts at a
key (or refines the key, for `promote`) using `Multiset.bind`/the `if`, both of
which send the empty multiset to the empty multiset. -/

theorem flatMap_preservesDisjoint (φ : K → Row H σ → Multiset (Row H' σ')) :
    PreservesDisjoint (flatMap φ) := by
  intro T₀ T₁ hdisj k
  rcases hdisj k with h | h
  · exact Or.inl (by simp [flatMap, h])
  · exact Or.inr (by simp [flatMap, h])

theorem flatMap_splitSafe (φ : K → Row H σ → Multiset (Row H' σ')) :
    SplitSafe (flatMap φ) := ⟨flatMap_preservesDisjoint φ, flatMap_splitInvariant φ⟩

theorem aggregate_preservesDisjoint (f : K → Multiset (Row H σ) → Row H σ) :
    PreservesDisjoint (aggregate f) := by
  intro T₀ T₁ hdisj k
  rcases hdisj k with h | h
  · exact Or.inl (by simp [aggregate, h])
  · exact Or.inr (by simp [aggregate, h])

theorem aggregate_splitSafe (f : K → Multiset (Row H σ) → Row H σ) :
    SplitSafe (aggregate f) := ⟨aggregate_preservesDisjoint f, aggregate_splitInvariant f⟩

theorem leftJoin_preservesDisjoint (key : K → U) (right : Table U G τ) :
    PreservesDisjoint (fun T => leftJoin (σ := σ) key T right) := by
  intro T₀ T₁ hdisj k
  rcases hdisj k with h | h
  · exact Or.inl (by simp [leftJoin, flatMap, h])
  · exact Or.inr (by simp [leftJoin, flatMap, h])

theorem leftJoin_splitSafe (key : K → U) (right : Table U G τ) :
    SplitSafe (fun T => leftJoin (σ := σ) key T right) :=
  ⟨leftJoin_preservesDisjoint key right, leftJoin_splitInvariant key right⟩

theorem innerJoin_preservesDisjoint (key : K → U) (right : Table U G τ) :
    PreservesDisjoint (fun T => innerJoin (σ := σ) key T right) := by
  intro T₀ T₁ hdisj k
  rcases hdisj k with h | h
  · exact Or.inl (by simp [innerJoin, flatMap, h])
  · exact Or.inr (by simp [innerJoin, flatMap, h])

theorem innerJoin_splitSafe (key : K → U) (right : Table U G τ) :
    SplitSafe (fun T => innerJoin (σ := σ) key T right) :=
  ⟨innerJoin_preservesDisjoint key right, innerJoin_splitInvariant key right⟩

theorem promote_preservesDisjoint {β : Type} [DecidableEq β] :
    PreservesDisjoint (promote (K := K) (H := H) (σ := σ) (β := β)) := by
  intro T₀ T₁ hdisj
  rintro ⟨k, v⟩
  rcases hdisj k with h | h
  · exact Or.inl (by simp [promote, h])
  · exact Or.inr (by simp [promote, h])

theorem promote_splitSafe {β : Type} [DecidableEq β] :
    SplitSafe (promote (K := K) (H := H) (σ := σ) (β := β)) :=
  ⟨promote_preservesDisjoint, promote_splitInvariant⟩

/-- A pipeline of split-safe operations is split-safe, hence split-invariant --
applying it between split and union equals applying it to the full table.  Here:
`flatMap`, then `leftJoin`, then `aggregate`. -/
example (φ : K → Row H σ → Multiset (Row H' σ')) (key : K → U) (right : Table U G τ)
    (g : K → Multiset (Row (H' ⊕ G) (Sum.elim σ' τ)) → Row (H' ⊕ G) (Sum.elim σ' τ)) :
    SplitSafe (aggregate g ∘ (fun T => leftJoin (σ := σ') key T right) ∘ flatMap φ) :=
  (aggregate_splitSafe g).comp ((leftJoin_splitSafe key right).comp (flatMap_splitSafe φ))

end SplitAlgebra
