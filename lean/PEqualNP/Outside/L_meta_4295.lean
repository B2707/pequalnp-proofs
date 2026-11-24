import Mathlib
import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112, by way of L-meta-2668.
namespace PEqualNP.Outside.L_meta_4295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CircuitMoves

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma gateAt_of_get {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

def lifted (n : ℕ) (C : Circuit) (m p h : ℕ) : Circuit :=
  ⟨(bypass n C m p).gates ++ [⟨GateOp.or, [(bypass n C m p).output, h]⟩],
    n + (bypass n C m p).gates.length⟩

lemma liftAt_eq (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    liftAt n C m p h = lifted n C m p h := by
  unfold liftAt lifted
  rw [erase_eq_bypass n C m p hm]

lemma lifted_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (lifted n C m p h).gates.length = C.gates.length := by
  simp [lifted, bypass]
  omega

lemma lifted_output (n : ℕ) (C : Circuit) (m p h : ℕ) :
    (lifted n C m p h).output = n + (C.gates.length - 1) := by
  simp [lifted, bypass]

lemma gateAt_lifted_lt {n : ℕ} {C : Circuit} {m p h k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (lifted n C m p h) k = gateAt (bypass n C m p) k := by
  have h1 : k < (bypass n C m p).gates.length := by rw [bypass_length]; exact hk
  simp only [gateAt, lifted, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h1]

lemma gateAt_lifted_last (n : ℕ) (C : Circuit) (m p h : ℕ) :
    gateAt (lifted n C m p h) (C.gates.length - 1) =
      ⟨GateOp.or, [aliasWire (n + m) p C.output, h]⟩ := by
  have h1 : (bypass n C m p).gates.length = C.gates.length - 1 := bypass_length n C m p
  simp only [gateAt, lifted, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), h1]
  simp [bypass]

lemma lifted_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m p h : ℕ}
    (hm : m < C.gates.length) :
    ∀ u, u < n + (C.gates.length - 1) →
      val (lifted n C m p h) x u = val (bypass n C m p) x u := by
  apply val_prefix hx (by rw [bypass_length]) (by rw [lifted_length n C m p h hm]; omega)
  intro k hk
  exact gateAt_lifted_lt hk

lemma lifted_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m p h : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length) :
    (lifted n C m p h).eval x = ((bypass n C m p).eval x || val C x h) := by
  have hL : C.gates.length - 1 < (lifted n C m p h).gates.length := by
    rw [lifted_length n C m p h hm]; omega
  have ha : aliasWire (n + m) p C.output < n + (C.gates.length - 1) :=
    aliasWire_lt hp (by omega) (by omega)
  have hh' : h < n + (C.gates.length - 1) := by omega
  rw [eval_eq_val, lifted_output, val_gate hx hL, gateAt_lifted_last]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
    Bool.or_false]
  rw [if_pos ha, if_pos hh', lifted_val_lt hx hm _ ha, lifted_val_lt hx hm _ hh',
    bypass_val_lt hx hm h hh, eval_eq_val, bypass_output]

lemma val_orgate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m p h : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hg : gateAt C m = ⟨GateOp.or, [p, h]⟩ ∨ gateAt C m = ⟨GateOp.or, [h, p]⟩) :
    val C x (n + m) = (val C x p || val C x h) := by
  rw [val_gate hx hm]
  rcases hg with hg | hg
  · rw [hg]
    simp [GateOp.eval, hp, hh]
  · rw [hg]
    simp [GateOp.eval, hp, hh, Bool.or_comm]

lemma lifted_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m p h : ℕ}
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length)
    (hg : gateAt C m = ⟨GateOp.or, [p, h]⟩ ∨ gateAt C m = ⟨GateOp.or, [h, p]⟩)
    (hw : val C x h = true → C.eval x = true) :
    (lifted n C m p h).eval x = C.eval x := by
  rw [lifted_eval hx hm hp hh hout]
  by_cases hv : val C x h = true
  · rw [hv, hw hv]
    simp
  · have hv' : val C x h = false := by simpa using hv
    rw [hv', Bool.or_false]
    apply bypass_eval_eq hx hAO hm (Or.inl hp)
    rw [val_orgate hx hm hp hh hg, hv', Bool.or_false]

lemma lifted_down {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {m p h : ℕ}
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hg : gateAt C m = ⟨GateOp.or, [p, h]⟩ ∨ gateAt C m = ⟨GateOp.or, [h, p]⟩)
    {v : ℕ} (hv : v < n + (C.gates.length - 1)) :
    val (lifted n C m p h) x v = true →
      val C x (if v < n + m then v else v + 1) = true := by
  rw [lifted_val_lt hx hm v hv]
  have key : val (bypass n C m p) x
      (aliasWire (n + m) p (if v < n + m then v else v + 1)) = true →
      val C x (if v < n + m then v else v + 1) = true :=
    bypass_rel (R := fun a b => b = true → a = true) (fun _ => id) opMono_reverse hx hAO hm
      (Or.inl hp)
      (fun _ => by rw [val_orgate hx hm hp hh hg]; intro h1; rw [h1]; rfl)
      (if v < n + m then v else v + 1) (by split_ifs <;> omega)
  have e : aliasWire (n + m) p (if v < n + m then v else v + 1) = v := by
    unfold aliasWire
    split_ifs <;> omega
  rw [e] at key
  exact key

lemma lifted_AO2 {n : ℕ} {C : Circuit} {m p h : ℕ} (hC : PEqualNP.TopForm.IsAO2 n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length) :
    PEqualNP.TopForm.IsAO2 n (lifted n C m p h) := by
  obtain ⟨hA, hR, hF⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [lifted, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
      rw [hop]
      exact hA g' hg'
    · exact Or.inr rfl
  · intro j hj i hi
    rw [lifted_length n C m p h hm] at hj
    by_cases hjl : j < C.gates.length - 1
    · rw [gateAt_lifted_lt hjl] at hi
      exact bypass_readsBack hp hR j (by rw [bypass_length]; exact hjl) i hi
    · have hje : j = C.gates.length - 1 := by omega
      subst hje
      rw [gateAt_lifted_last] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact aliasWire_lt hp (by omega) (by omega)
      · omega
  · intro g hg
    simp only [lifted, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨g', hg', _, hlen⟩ := bypass_mem g hg
      rw [hlen]
      exact hF g' hg'
    · rfl

def bad (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => ¬ WireBelowOutput n C (n + j))

lemma bad_lt {n : ℕ} {C : Circuit} {m p h : ℕ} (hC : PEqualNP.TopForm.IsAO2 n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length)
    (hg : gateAt C m = ⟨GateOp.or, [p, h]⟩ ∨ gateAt C m = ⟨GateOp.or, [h, p]⟩)
    (hwh : WireBelowOutput n C h) (hnp : ¬ WireBelowOutput n C p) :
    (bad n (lifted n C m p h)).card < (bad n C).card := by
  have hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => hC.1 _ (gateAt_mem hk)
  have hev : ∀ x : Fin n → Bool,
      (lifted n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) :=
    fun x => lifted_eval_eq (by simp) hAO hm hp hh hout hg (hwh x)
  have hmbad : m ∈ bad n C := by
    simp only [bad, Finset.mem_filter, Finset.mem_range]
    refine ⟨hm, fun hw => hnp (fun x hx => hw x ?_)⟩
    change val C (List.ofFn x) (n + m) = true
    rw [val_orgate (by simp) hm hp hh hg]
    change val C (List.ofFn x) p = true at hx
    rw [hx]
    rfl
  have hsub : ∀ j ∈ bad n (lifted n C m p h),
      (if j < m then j else j + 1) ∈ (bad n C).erase m := by
    intro j hj
    simp only [bad, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjl, hjb⟩ := hj
    rw [lifted_length n C m p h hm] at hjl
    have hjne : j ≠ C.gates.length - 1 := by
      rintro rfl
      apply hjb
      intro x hx
      rw [eval_eq_val, lifted_output]
      exact hx
    have hjl' : j < C.gates.length - 1 := by omega
    simp only [bad, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    intro hw
    apply hjb
    intro x hx
    rw [hev x]
    apply hw x
    have key := lifted_down (x := List.ofFn x) (by simp) hAO hm hp hh hg (v := n + j)
      (by omega) hx
    have e : (if n + j < n + m then n + j else n + j + 1) =
        n + (if j < m then j else j + 1) := by
      split_ifs <;> omega
    rw [e] at key
    exact key
  have hinj : Set.InjOn (fun j => if j < m then j else j + 1)
      (bad n (lifted n C m p h) : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    split_ifs at hab <;> omega
  calc (bad n (lifted n C m p h)).card ≤ ((bad n C).erase m).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ < (bad n C).card := Finset.card_erase_lt_of_mem hmbad

lemma main (n : ℕ) : ∀ (k : ℕ) (C : Circuit), (bad n C).card = k →
    PEqualNP.TopForm.IsAO2 n C → C.output < n + C.gates.length →
    ∃ C' : Circuit, Relation.ReflTransGen (Lift n) C C' ∧
      ∀ j < C'.gates.length, ∀ a b : ℕ, C'.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C' b → WireBelowOutput n C' a) ∧
        (n ≤ a → WireBelowOutput n C' a → WireBelowOutput n C' b) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hout
    by_cases hex : ∃ j < C.gates.length, ∃ p h : ℕ,
        (C.gates[j]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[j]? = some ⟨GateOp.or, [h, p]⟩) ∧
        n ≤ h ∧ WireBelowOutput n C h ∧ ¬ WireBelowOutput n C p
    · obtain ⟨j, hj, p, h, hg, hnh, hwh, hnp⟩ := hex
      have hg' : gateAt C j = ⟨GateOp.or, [p, h]⟩ ∨ gateAt C j = ⟨GateOp.or, [h, p]⟩ := by
        rcases hg with hg | hg
        · exact Or.inl (gateAt_of_get hg)
        · exact Or.inr (gateAt_of_get hg)
      have hp : p < n + j := by
        apply hC.2.1 j hj
        rcases hg' with hg' | hg' <;> rw [hg'] <;> simp
      have hh : h < n + j := by
        apply hC.2.1 j hj
        rcases hg' with hg' | hg' <;> rw [hg'] <;> simp
      have hlift : Lift n C (lifted n C j p h) :=
        ⟨j, hj, p, hp, h, hh, hnh, hg, hwh, (liftAt_eq n C j p h hj).symm⟩
      have hlt := bad_lt hC hj hp hh hout hg' hwh hnp
      rw [hk] at hlt
      have hout' : (lifted n C j p h).output < n + (lifted n C j p h).gates.length := by
        rw [lifted_output, lifted_length n C j p h hj]
        omega
      obtain ⟨C', hR, hfix⟩ := ih _ hlt (lifted n C j p h) rfl
        (lifted_AO2 hC hj hp hh hout) hout'
      exact ⟨C', Relation.ReflTransGen.head hlift hR, hfix⟩
    · refine ⟨C, Relation.ReflTransGen.refl, ?_⟩
      intro j hj a b hg
      constructor
      · intro hb hwb
        by_contra hna
        exact hex ⟨j, hj, a, b, Or.inl hg, hb, hwb, hna⟩
      · intro ha hwa
        by_contra hnb
        exact hex ⟨j, hj, b, a, Or.inr hg, ha, hwa, hnb⟩

end PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hC hout
  exact PEqualNP.Outside.L_meta_4295.main n _ C rfl hC hout
