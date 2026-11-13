import SplitAlgebra.SplitSafety
import SplitAlgebra.Completeness.FiberMap

/-!
Binary joins: both arguments are tables, and either may be split.

The four-term statement (`FourTerm`) puts the cross terms `f T₀ R₁` on the right
side, which is exactly the leakage the algebra rules out; the statement that
matches the semantics of a split is the *aligned diagonal law* (`AlignedDiagonal`),
where a split of the universe routes each entity, with its rows in every table, to
one side.

Results:

- `innerJoin_bihom`: the inner join is bilinear, hence satisfies the four-term
  statement unconditionally.
- `leftJoin_not_splitInvariant_right`, `leftJoin_not_fourTerm`: the left join is
  invariant in the left argument only.
- `innerJoin_alignedDiagonal`, `leftJoin_alignedDiagonal`: under alignment both
  joins satisfy the diagonal law; `innerJoin_not_alignedDiagonal`,
  `leftJoin_not_alignedDiagonal` show alignment is necessary.
- `alignedDiagonal_biKeyLocal_iff_biFiberMap`: binary safe completeness.
-/

namespace SplitAlgebra

variable {K H : Type _} {σ : H → Type}
variable {H' : Type _} {σ' : H' → Type}
variable {U G : Type _} {τ : G → Type}

/-! ## The four-term statement -/

/-- The natural statement: on disjoint halves in both arguments, the join of the
unions is the union of the four joins of the halves. -/
def FourTerm {K' : Type _} (f : Table K H σ → Table U G τ → Table K' H' σ') : Prop :=
  ∀ T₀ T₁ R₀ R₁, Disjoint T₀ T₁ → Disjoint R₀ R₁ →
    f (union T₀ T₁) (union R₀ R₁)
      = union (union (f T₀ R₀) (f T₀ R₁)) (union (f T₁ R₀) (f T₁ R₁))

/-- A bihomomorphism satisfies the four-term statement with no disjointness. -/
def BiHom {K' : Type _} (f : Table K H σ → Table U G τ → Table K' H' σ') : Prop :=
  ∀ T₀ T₁ R₀ R₁,
    f (union T₀ T₁) (union R₀ R₁)
      = union (union (f T₀ R₀) (f T₀ R₁)) (union (f T₁ R₀) (f T₁ R₁))

theorem BiHom.fourTerm {K' : Type _} {f : Table K H σ → Table U G τ → Table K' H' σ'}
    (h : BiHom f) : FourTerm f :=
  fun T₀ T₁ R₀ R₁ _ _ => h T₀ T₁ R₀ R₁

/-- The inner join is bilinear: the per-key cross product distributes over the
multiset sum in each argument. -/
theorem innerJoin_bihom (key : K → U) :
    BiHom (innerJoin (H := H) (σ := σ) (G := G) (τ := τ) key) := by
  intro T₀ T₁ R₀ R₁
  apply Table.ext_rows
  intro k
  simp only [innerJoin, flatMap, union, Multiset.add_bind,
    Multiset.map_add, Multiset.bind_add]
  abel

/-- `innerJoin` is a union homomorphism in the right argument. -/
theorem innerJoin_unionHom_right (key : K → U) (T : Table K H σ) :
    UnionHom (fun R : Table U G τ => innerJoin key T R) := by
  intro R₀ R₁
  apply Table.ext_rows
  intro k
  simp only [innerJoin, flatMap, union, Multiset.map_add, Multiset.bind_add]

section LeftJoinCounterexample

/-- The unit row. -/
private def unitRow : Row Unit (fun _ : Unit => Unit) := fun _ => some ()

private def oneRow : Table Unit Unit (fun _ : Unit => Unit) := ⟨fun _ => {unitRow}⟩

private def zeroTab : Table Unit Unit (fun _ : Unit => Unit) := ⟨fun _ => 0⟩

/-- The left join is not split invariant in its right argument: a left row matched
in one half of the reference and unmatched in the other receives both a value and
a missing marker. -/
theorem leftJoin_not_splitInvariant_right :
    ∃ (T : Table Unit Unit (fun _ : Unit => Unit)),
      ¬ SplitInvariant (fun R : Table Unit Unit (fun _ : Unit => Unit) =>
        leftJoin (id : Unit → Unit) T R) := by
  refine ⟨oneRow, fun h => ?_⟩
  have hd : Disjoint oneRow zeroTab := fun _ => Or.inr rfl
  have e := h oneRow zeroTab hd
  have hu : union oneRow zeroTab = oneRow := by
    apply Table.ext_rows; intro k; simp [union, oneRow, zeroTab]
  rw [hu] at e
  have := congrArg (fun X => (X.rows ()).card) e
  simp [leftJoin, flatMap, union, oneRow, zeroTab] at this

/-- The left join fails the four-term statement. -/
theorem leftJoin_not_fourTerm :
    ¬ FourTerm (leftJoin (K := Unit) (U := Unit) (H := Unit) (σ := fun _ : Unit => Unit)
      (G := Unit) (τ := fun _ : Unit => Unit) id) := by
  intro h
  have hd₁ : Disjoint zeroTab oneRow := fun _ => Or.inl rfl
  have hd₂ : Disjoint oneRow zeroTab := fun _ => Or.inr rfl
  have e := h oneRow zeroTab oneRow zeroTab hd₂ hd₂
  have hu : union oneRow zeroTab = oneRow := by
    apply Table.ext_rows; intro k; simp [union, oneRow, zeroTab]
  rw [hu] at e
  have := congrArg (fun X => (X.rows ()).card) e
  simp [leftJoin, flatMap, union, oneRow, zeroTab] at this

end LeftJoinCounterexample

/-! ## Aligned splits and the diagonal law -/

/-- Indicators on the left and right keys are aligned when the right indicator is
the left one composed with `key`: an entity goes to the same side in both tables. -/
def Aligned (key : K → U) (s : K → Bool) (sR : U → Bool) : Prop :=
  ∀ k, s k = sR (key k)

/-- The aligned diagonal law: for every aligned split, the join of the whole is the
union of the joins of the matching halves. -/
def AlignedDiagonal {K' : Type _} (key : K → U)
    (f : Table K H σ → Table U G τ → Table K' H' σ') : Prop :=
  ∀ (s : K → Bool) (sR : U → Bool), Aligned key s sR → ∀ T R,
    f T R = union (f (split s T).1 (split sR R).1) (f (split s T).2 (split sR R).2)

/-- Binary fibre maps: the output bag at `k` depends on the left bag at `k` and the
right bag at `key k`. -/
def biFiberMap (key : K → U)
    (Φ : K → Multiset (Row H σ) → Multiset (Row G τ) → Multiset (Row H' σ'))
    (T : Table K H σ) (R : Table U G τ) : Table K H' σ' :=
  ⟨fun k => Φ k (T.rows k) (R.rows (key k))⟩

/-- Joint strictness: no rows are fabricated when both fibres are empty. -/
def JointlyStrict (Φ : K → Multiset (Row H σ) → Multiset (Row G τ) → Multiset (Row H' σ')) :
    Prop :=
  ∀ k, Φ k 0 0 = 0

/-- Binary key-locality. -/
def BiKeyLocal (key : K → U) (f : Table K H σ → Table U G τ → Table K H' σ') : Prop :=
  ∀ (T T' : Table K H σ) (R R' : Table U G τ) (k : K),
    T.rows k = T'.rows k → R.rows (key k) = R'.rows (key k) →
      (f T R).rows k = (f T' R').rows k

theorem biFiberMap_biKeyLocal (key : K → U)
    (Φ : K → Multiset (Row H σ) → Multiset (Row G τ) → Multiset (Row H' σ')) :
    BiKeyLocal key (biFiberMap key Φ) := by
  intro T T' R R' k hT hR
  simp only [biFiberMap, hT, hR]

/-- Splitting the zero table gives zero tables. -/
private theorem split_zero (s : K → Bool) :
    split s (⟨fun _ => 0⟩ : Table K H σ) = (⟨fun _ => 0⟩, ⟨fun _ => 0⟩) := by
  simp only [split, Prod.mk.injEq]
  constructor <;> (apply Table.ext_rows; intro k; cases s k <;> simp)

/-- The diagonal law forces the join of empty tables to be empty. -/
theorem AlignedDiagonal.map_zero {key : K → U}
    {f : Table K H σ → Table U G τ → Table K H' σ'} (hf : AlignedDiagonal key f) (k : K) :
    (f ⟨fun _ => 0⟩ ⟨fun _ => 0⟩).rows k = 0 := by
  have e := hf (fun _ => false) (fun _ => false) (fun _ => rfl) ⟨fun _ => 0⟩ ⟨fun _ => 0⟩
  rw [split_zero, split_zero] at e
  have hrow := congrArg (fun X => X.rows k) e
  simp only [union] at hrow
  exact multiset_self_add (by simpa using hrow)

/-- A jointly strict binary fibre map satisfies the aligned diagonal law. -/
theorem biFiberMap_alignedDiagonal (key : K → U)
    {Φ : K → Multiset (Row H σ) → Multiset (Row G τ) → Multiset (Row H' σ')}
    (hΦ : JointlyStrict Φ) : AlignedDiagonal key (biFiberMap key Φ) := by
  intro s sR hal T R
  apply Table.ext_rows
  intro k
  have := hal k
  simp only [biFiberMap, union, split]
  cases hs : s k <;> rw [hs] at this <;> rw [← this] <;> simp [hΦ k]

/-- Under alignment the two halves of the result are disjoint, so the binary
operation is split safe. -/
theorem biFiberMap_aligned_disjoint (key : K → U)
    {Φ : K → Multiset (Row H σ) → Multiset (Row G τ) → Multiset (Row H' σ')}
    (hΦ : JointlyStrict Φ) {s : K → Bool} {sR : U → Bool} (hal : Aligned key s sR)
    (T : Table K H σ) (R : Table U G τ) :
    Disjoint (biFiberMap key Φ (split s T).1 (split sR R).1)
      (biFiberMap key Φ (split s T).2 (split sR R).2) := by
  intro k
  have := hal k
  simp only [biFiberMap, split]
  cases hs : s k <;> rw [hs] at this <;> rw [← this] <;> simp [hΦ k]

/-- **Binary safe completeness.**  A binary operation is bi-key-local and satisfies
the aligned diagonal law iff it is a jointly strict binary fibre map. -/
theorem alignedDiagonal_biKeyLocal_iff_biFiberMap [DecidableEq K] [DecidableEq U]
    {key : K → U} {f : Table K H σ → Table U G τ → Table K H' σ'} :
    (AlignedDiagonal key f ∧ BiKeyLocal key f) ↔
      ∃ Φ, JointlyStrict Φ ∧ f = biFiberMap key Φ := by
  constructor
  · rintro ⟨hAD, hKL⟩
    refine ⟨fun k m n => (f (pointTable k m) (pointTable (key k) n)).rows k, ?_, ?_⟩
    · intro k
      have hT : pointTable k (0 : Multiset (Row H σ)) = ⟨fun _ => 0⟩ := by
        apply Table.ext_rows; intro k'; simp [pointTable]
      have hR : pointTable (key k) (0 : Multiset (Row G τ)) = ⟨fun _ => 0⟩ := by
        apply Table.ext_rows; intro k'; simp [pointTable]
      simp only [hT, hR]
      exact hAD.map_zero k
    · funext T R
      apply Table.ext_rows
      intro k
      exact hKL T (pointTable k (T.rows k)) R (pointTable (key k) (R.rows (key k))) k
        (by simp) (by simp)
  · rintro ⟨Φ, hΦ, rfl⟩
    exact ⟨biFiberMap_alignedDiagonal key hΦ, biFiberMap_biKeyLocal key Φ⟩

/-! ## The joins as binary fibre maps -/

theorem innerJoin_eq_biFiberMap (key : K → U) :
    innerJoin (H := H) (σ := σ) (G := G) (τ := τ) key
      = biFiberMap key (fun _ m n => m.bind (fun f => n.map (fun r => f.elim r))) := rfl

theorem leftJoin_eq_biFiberMap (key : K → U) :
    leftJoin (H := H) (σ := σ) (G := G) (τ := τ) key
      = biFiberMap key (fun _ m n => m.bind (fun f =>
          if n.card = 0 then {f.elim (fun _ => none)} else n.map (fun r => f.elim r))) := rfl

theorem innerJoin_alignedDiagonal (key : K → U) :
    AlignedDiagonal key (innerJoin (H := H) (σ := σ) (G := G) (τ := τ) key) := by
  rw [innerJoin_eq_biFiberMap]
  exact biFiberMap_alignedDiagonal key (fun k => by simp)

theorem leftJoin_alignedDiagonal (key : K → U) :
    AlignedDiagonal key (leftJoin (H := H) (σ := σ) (G := G) (τ := τ) key) := by
  rw [leftJoin_eq_biFiberMap]
  exact biFiberMap_alignedDiagonal key (fun k => by simp)

/-! ## Alignment is necessary -/

section Unaligned

private def uRow : Row Unit (fun _ : Unit => Unit) := fun _ => some ()

private def uOne : Table Unit Unit (fun _ : Unit => Unit) := ⟨fun _ => {uRow}⟩

/-- Without alignment (left entity to side 0, reference row to side 1) the inner
join fails the diagonal law. -/
theorem innerJoin_not_alignedDiagonal :
    ∃ (s : Unit → Bool) (sR : Unit → Bool), ¬ Aligned (id : Unit → Unit) s sR ∧
      ∃ T R, innerJoin (id : Unit → Unit) T (R : Table Unit Unit (fun _ : Unit => Unit))
        ≠ union (innerJoin id (split s T).1 (split sR R).1)
                (innerJoin id (split s (T : Table Unit Unit (fun _ : Unit => Unit))).2
                  (split sR R).2) := by
  refine ⟨fun _ => false, fun _ => true, fun h => by simpa using h (), uOne, uOne, fun e => ?_⟩
  have := congrArg (fun X => (X.rows ()).card) e
  simp [innerJoin, flatMap, union, split, uOne] at this

/-- Likewise for the left join. -/
theorem leftJoin_not_alignedDiagonal :
    ∃ (s : Unit → Bool) (sR : Unit → Bool), ¬ Aligned (id : Unit → Unit) s sR ∧
      ∃ T R, leftJoin (id : Unit → Unit) T (R : Table Unit Unit (fun _ : Unit => Unit))
        ≠ union (leftJoin id (split s T).1 (split sR R).1)
                (leftJoin id (split s (T : Table Unit Unit (fun _ : Unit => Unit))).2
                  (split sR R).2) := by
  refine ⟨fun _ => false, fun _ => true, fun h => by simpa using h (), uOne, uOne, fun e => ?_⟩
  have := congrArg (fun X => X.rows ()) e
  simp [leftJoin, flatMap, union, split, uOne] at this
  have := congrFun this (Sum.inr ())
  simp [Row.elim, uRow] at this

end Unaligned

end SplitAlgebra
