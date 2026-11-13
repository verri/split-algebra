/-
Reshape: `unpivotKeepMissing` (wide-to-long), `pivotKey` (long-to-wide), and the
drop-variant `unpivot` that makes the pair mutually inverse.

Main Source:  Chapter 5 of F. A. N. Verri (2026). Data Science Project: An
Inductive Learning Approach. Version v1.0.0. Victoria, British Columbia,
Canada: Leanpub. doi: 10.5281/zenodo.18815798. url: https://leanpub.com/dsp.

`unpivotKeepMissing` and `unpivot` are split-safe; `pivotKey` is *not even*
split-invariant (a name-separating split breaks it), which refines the book:
its pivotKey split-invariance relies on cell-wise-merge union over ragged cells,
which this total-row / union-union model deliberately does not have.  The
inverse results: `pivotKey_unpivotReify` (reify variant, functional tables),
and the mutually inverse drop pair `pivotKey_unpivot` / `unpivot_pivotKey`
on functional minimal tables, the long-to-wide-to-long direction carrying no
completeness side condition.
-/

import SplitAlgebra.Core.Defs

namespace SplitAlgebra

variable {K : Type _}
variable {N : Type _} {V : Type}

/-- Read the one value out of a card-≤1 bag of single-column rows (`none` when
empty).  `noncomputable` (uses `Multiset.toList`), which is fine for this
proof-only development; execution lives in the runtime layer. -/
noncomputable def cellOf (m : Multiset (Row Unit (fun _ => V))) : Cell V :=
  (m.toList.head?).elim none (fun g => g ())

@[simp] theorem cellOf_zero :
    cellOf (0 : Multiset (Row Unit (fun _ => V))) = none := by
  simp [cellOf, Multiset.toList_zero]

@[simp] theorem cellOf_singleton (g : Row Unit (fun _ => V)) :
    cellOf {g} = g () := by
  simp [cellOf, Multiset.toList_singleton]

/-- def:pivot-w2l (unpivotKeepMissing, wide-to-long).  Spread each name-column `n` of a wide
row into its own output key `(k, n)`, carrying that column's value.  A flatMap-like
operation, hence a `UnionHom` and `SplitSafe` -- the safe reshape direction. -/
def unpivotKeepMissing (T : Table K N (fun _ => V)) : Table (K × N) Unit (fun _ => V) :=
  ⟨fun p => (T.rows p.1).map (fun f => fun _ => f p.2)⟩

/-- def:pivot-l2w (pivotKey, long-to-wide).  Gather the value at each name `n` into
one wide row per key `k`; a key whose names are all empty stays absent (matching
the chapter's minimality).  A canonical value exists only at card ≤ 1 per
`(k, n)` (the chapter's "card constant"), so `cellOf` is used.  Unlike `unpivotKeepMissing`,
`pivotKey` is *not* split-invariant (`pivotKey_not_splitInvariant`). -/
noncomputable def pivotKey [Fintype N] (T : Table (K × N) Unit (fun _ => V)) :
    Table K N (fun _ => V) :=
  ⟨fun k => if (∀ n, (T.rows (k, n)).card = 0) then 0
            else {fun n => cellOf (T.rows (k, n))}⟩

/-- A table is functional when every key holds at most one nested row. -/
def Functional {H : Type _} {σ : H → Type} (T : Table K H σ) : Prop :=
  ∀ k, (T.rows k).card ≤ 1

/-! ### Reshape: unpivotKeepMissing is split-safe, pivotKey is not, and they are inverses -/

/-- `unpivotKeepMissing` is a union-homomorphism (it is flatMap-like over the input key). -/
theorem unpivotKeepMissing_unionHom : UnionHom (unpivotKeepMissing (K := K) (N := N) (V := V)) := by
  intro T₀ T₁
  apply Table.ext_rows
  rintro ⟨k, n⟩
  simp only [unpivotKeepMissing, union]
  exact Multiset.map_add _ _ _

theorem unpivotKeepMissing_preservesDisjoint :
    PreservesDisjoint (unpivotKeepMissing (K := K) (N := N) (V := V)) := by
  intro T₀ T₁ hdisj
  rintro ⟨k, n⟩
  rcases hdisj k with h | h
  · exact Or.inl (by simp [unpivotKeepMissing, h])
  · exact Or.inr (by simp [unpivotKeepMissing, h])

/-- Hence `unpivotKeepMissing` is split-safe -- the safe reshape direction. -/
theorem unpivotKeepMissing_splitSafe : SplitSafe (unpivotKeepMissing (K := K) (N := N) (V := V)) :=
  ⟨unpivotKeepMissing_preservesDisjoint, unpivotKeepMissing_unionHom.splitInvariant⟩

/-- `pivotKey` is *not* split-invariant: a split that separates the names of one key
yields two complementary partial rows that union-`union` keeps apart (card 1 on
the left, card 2 on the right).  This refines the book, whose pivotKey
split-invariance relies on cell-wise-merge union over ragged cells -- which this
total-row / union-union model deliberately does not have. -/
theorem pivotKey_not_splitInvariant :
    ¬ SplitInvariant (pivotKey (K := Unit) (N := Bool) (V := Unit)) := by
  intro h
  have hd := h
    ⟨fun p => if p.2 then 0 else {fun _ => none}⟩
    ⟨fun p => if p.2 then {fun _ => none} else 0⟩
    (by intro p; cases hp : p.2 <;> simp [hp])
  apply_fun (fun U => (U.rows ()).card) at hd
  simp [pivotKey, union, Bool.forall_bool] at hd

/-- `pivotKey` does not preserve disjointness either: on the same name-separating
split, both halves pivot to a row at the one residual key.  The two failures are
independent of each other. -/
theorem pivotKey_not_preservesDisjoint :
    ¬ PreservesDisjoint (pivotKey (K := Unit) (N := Bool) (V := Unit)) := by
  intro h
  have hd := h
    ⟨fun p => if p.2 then 0 else {fun _ => none}⟩
    ⟨fun p => if p.2 then {fun _ => none} else 0⟩
    (by intro p; cases hp : p.2 <;> simp [hp]) ()
  simp [pivotKey, Bool.forall_bool] at hd

/-- def:pivot inverts def:pivot-w2l on functional tables (the "card constant"
case): pivoting an unpivoted wide table recovers it.  This reversibility is the
reason pivotKey is useful despite not being split-invariant. -/
theorem pivotKey_unpivotReify [Fintype N] [Nonempty N] {T : Table K N (fun _ => V)}
    (hT : Functional T) : pivotKey (unpivotKeepMissing T) = T := by
  apply Table.ext_rows
  intro k
  rcases Nat.lt_or_ge (T.rows k).card 1 with hc | hc
  · have h0 : T.rows k = 0 := Multiset.card_eq_zero.mp (by omega)
    simp [pivotKey, unpivotKeepMissing, h0]
  · have hc1 : (T.rows k).card = 1 := le_antisymm (hT k) hc
    obtain ⟨f, hf⟩ := Multiset.card_eq_one.mp hc1
    obtain ⟨n₀⟩ := (inferInstance : Nonempty N)
    have hguard : ¬ (∀ n, ((unpivotKeepMissing T).rows (k, n)).card = 0) := by
      intro hall
      have h1 := hall n₀
      simp [unpivotKeepMissing, hf] at h1
    simp only [pivotKey]
    rw [if_neg hguard]
    simp [unpivotKeepMissing, hf, Multiset.map_singleton]

/-! ### The drop variant `unpivot`: a truly inverse pair

`unpivotKeepMissing` above *reifies* a missing wide cell as a long row holding `none`.
That asymmetry is what blocks the long-to-wide-to-long round trip on sparse
tables: `pivotKey` sends an absent row to a missing cell, and the reify
variant sends the missing cell back to a *present* row, fabricating rows
the sparse table never had.  The drop variant
removes the
asymmetry: a missing cell yields no long row, so value-missing in the wide
table and row-absent in the long table carry the same information, and the
pair becomes mutually inverse on functional, minimal tables -- with no
completeness or saturation side condition in either direction. -/

/-- The drop variant of def:pivot-w2l: spread each name-column
`n` of a wide row into its own output key `(k, n)`, emitting a long row
only when the cell is present.  The long value column is total by
construction.  Being `Multiset.bind`-shaped per output key over a single
input key (compare `promote`), it is a union-homomorphism, hence
split-safe. -/
def unpivot (T : Table K N (fun _ => V)) : Table (K × N) Unit (fun _ => V) :=
  ⟨fun p => (T.rows p.1).bind (fun f =>
    match f p.2 with
    | some v => {fun _ => some v}
    | none => 0)⟩

/-- `unpivot` is a union-homomorphism: the drop is decided per input
row, so it distributes over every union. -/
theorem unpivot_unionHom : UnionHom (unpivot (K := K) (N := N) (V := V)) := by
  intro T₀ T₁
  apply Table.ext_rows
  rintro ⟨k, n⟩
  simp only [unpivot, union]
  exact Multiset.add_bind _ _ _

theorem unpivot_preservesDisjoint :
    PreservesDisjoint (unpivot (K := K) (N := N) (V := V)) := by
  intro T₀ T₁ hdisj
  rintro ⟨k, n⟩
  rcases hdisj k with h | h
  · exact Or.inl (by simp [unpivot, h])
  · exact Or.inr (by simp [unpivot, h])

/-- `unpivot` is split-safe, like the reify variant: dropping a missing
cell is a per-row decision. -/
theorem unpivot_splitSafe : SplitSafe (unpivot (K := K) (N := N) (V := V)) :=
  ⟨unpivot_preservesDisjoint, unpivot_unionHom.splitInvariant⟩

/-- `pivotKey` inverts `unpivot` on functional, **minimal** wide tables.
Minimality is load-bearing where it was not for the reify variant
(`pivotKey_unpivotReify`): a wide row whose cells are all missing yields no long
rows, so its key would vanish; the chapter's standing minimality
assumption rules exactly those rows out (the rule "at least one total
folded column" is the surface approximation of it). -/
theorem pivotKey_unpivot [Fintype N] {T : Table K N (fun _ => V)}
    (hT : Functional T) (hM : Minimal T) : pivotKey (unpivot T) = T := by
  apply Table.ext_rows
  intro k
  rcases Nat.lt_or_ge (T.rows k).card 1 with hc | hc
  · have h0 : T.rows k = 0 := Multiset.card_eq_zero.mp (by omega)
    simp [pivotKey, unpivot, h0]
  · have hc1 : (T.rows k).card = 1 := le_antisymm (hT k) hc
    obtain ⟨f, hf⟩ := Multiset.card_eq_one.mp hc1
    obtain ⟨n₀, hn₀⟩ := hM k f (by rw [hf]; exact Multiset.mem_singleton_self f)
    obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp hn₀
    have hguard : ¬ (∀ n, ((unpivot T).rows (k, n)).card = 0) := by
      intro hall
      have h1 := hall n₀
      simp [unpivot, hf, hv₀] at h1
    simp only [pivotKey]
    rw [if_neg hguard, hf, Multiset.singleton_inj]
    funext n
    cases hfn : f n <;> simp [unpivot, hf, hfn]

/-- `unpivot` inverts `pivotKey` on functional, minimal long tables --
with **no completeness or saturation side condition**: an absent `(k, n)`
row pivots to a missing cell, which the drop variant sends back to an
absent row, so a sparse long table round-trips as it is.  This direction
is not statable for the reify variant, and it is the mechanized content of
the inverse contract.  Minimality here says every long row's value
is known, which is the invariant `unpivot`'s own output satisfies by
construction. -/
theorem unpivot_pivotKey [Fintype N] {L : Table (K × N) Unit (fun _ => V)}
    (hL : Functional L) (hM : Minimal L) : unpivot (pivotKey L) = L := by
  apply Table.ext_rows
  rintro ⟨k, n⟩
  by_cases hg : ∀ n', (L.rows (k, n')).card = 0
  · -- Every fiber at `k` is empty: both sides are empty at `(k, n)`.
    have h0 : L.rows (k, n) = 0 := Multiset.card_eq_zero.mp (hg n)
    simp [unpivot, pivotKey, hg, h0]
  · -- Some fiber is present: the one wide row reads back cell by cell.
    rcases Nat.lt_or_ge (L.rows (k, n)).card 1 with hc | hc
    · have h0 : L.rows (k, n) = 0 := Multiset.card_eq_zero.mp (by omega)
      simp only [unpivot, pivotKey]
      rw [if_neg hg]
      simp [h0]
    · have hc1 : (L.rows (k, n)).card = 1 := le_antisymm (hL (k, n)) hc
      obtain ⟨g, hgrow⟩ := Multiset.card_eq_one.mp hc1
      obtain ⟨u, hu⟩ := hM (k, n) g (by rw [hgrow]; exact Multiset.mem_singleton_self g)
      have hu' : g () ≠ none := by cases u; exact hu
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hu'
      simp only [unpivot, pivotKey]
      rw [if_neg hg]
      have hcell : cellOf (L.rows (k, n)) = some v := by
        rw [hgrow, cellOf_singleton, hv]
      simp only [Multiset.singleton_bind, hcell]
      rw [hgrow, Multiset.singleton_inj]
      funext u'
      cases u'
      exact hv.symm

end SplitAlgebra
