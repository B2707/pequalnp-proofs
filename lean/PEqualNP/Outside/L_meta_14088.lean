import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14088

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedSlice

abbrev Signal (α : Type) := α → Bool
def inv {α} (a : Signal α) : Signal α := fun x => !(a x)
def meet {α} (a b : Signal α) : Signal α := fun x => a x && b x

inductive Run {α : Type} (start : List (Signal α)) : ℕ → List (Signal α) → Prop where
  | nil : Run start 0 start
  | gate {k w} (h : Run start k w) {a b} (ha : a ∈ w) (hb : b ∈ w) :
      Run start (k+1) (w ++ [meet a b, inv (meet a b)])

theorem Run.keep {α} {s w : List (Signal α)} {k} (h : Run s k w) :
    ∀ v ∈ s, v ∈ w := by
  induction h with
  | nil => exact fun _ h => h
  | gate h _ _ ih => exact fun v hv => List.mem_append_left _ (ih v hv)

theorem Run.comp {α} {s w u : List (Signal α)} {k j} (h : Run s k w) (h' : Run w j u) :
    Run s (k+j) u := by
  induction h' with
  | nil => exact h
  | gate h' ha hb ih => exact Run.gate ih ha hb

structure Wire (α : Type) where
  f : Signal α
  lo : Bool
  hi : Bool

def K {α} (b : Bool) : Wire α := ⟨fun _ => b,b,b⟩
def neg {α} (a : Wire α) : Wire α := ⟨inv a.f,!a.lo,!a.hi⟩
def conj {α} (a b : Wire α) : Wire α := ⟨meet a.f b.f,a.lo && b.lo,a.hi && b.hi⟩
def disj {α} (a b : Wire α) : Wire α := neg (conj (neg a) (neg b))

def Good {α} (w : List (Signal α)) (a : Wire α) : Prop := a.f ∈ w ∧ inv a.f ∈ w
def Stable {α} (a : Wire α) : Prop := (∃ b, ∀ x, a.f x = b) ∨ a.lo = a.hi

theorem goodNeg {α} {w : List (Signal α)} {a} (h : Good w a) : Good w (neg a) := by
  refine ⟨h.2,?_⟩
  have eq : inv (inv a.f) = a.f := by funext x; simp [inv]
  change inv (inv a.f) ∈ w
  rw [eq]
  exact h.1

theorem stableNeg {α} {a : Wire α} (h : Stable a) : Stable (neg a) := by
  rcases h with ⟨b,hb⟩ | eq
  · exact Or.inl ⟨!b,fun x => by simp [neg,inv,hb]⟩
  · exact Or.inr (congrArg Bool.not eq)

def Eval {α} (op : GateOp) (args : List (Wire α)) : Wire α :=
  ⟨fun x => op.eval (args.map fun a => a.f x),op.eval (args.map Wire.lo),op.eval (args.map Wire.hi)⟩

def Paid (g : Gate) : ℕ :=
  if g.op.eval [false] then 0 else if g.inputs.length = 2 then 1 else 0

def Effect {α} (w : List (Signal α)) (n : ℕ) (a : Wire α) (inputs : List (Wire α)) : Prop :=
  ∃ c t, Run w c t ∧ c ≤ n ∧ Good t a ∧
    (c = n → (∀ u ∈ inputs, Stable u) → Stable a)

private theorem bin {α} (w : List (Signal α)) (base : ∀ b, Good w (K b)) (a b : Wire α)
    (ha : Good w a) (hb : Good w b) : Effect w 1 (conj a b) [a,b] := by
  classical
  by_cases ca : ∃ t, ∀ x, a.f x = t
  · obtain ⟨t,e⟩ := ca
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = b.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using hb
  by_cases cb : ∃ t, ∀ x, b.f x = t
  · obtain ⟨t,e⟩ := cb
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = a.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using ha
  · refine ⟨1,_,Run.gate Run.nil ha.1 hb.1,le_rfl,?_,?_⟩
    · exact ⟨List.mem_append_right _ (by simp [conj]),List.mem_append_right _ (by simp [conj])⟩
    · intro _ stable
      have ea := (stable a (by simp)).resolve_left ca
      have eb := (stable b (by simp)).resolve_left cb
      exact Or.inr (by simp [conj,ea,eb])

private theorem gateEffect {α} (w : List (Signal α)) (base : ∀ b, Good w (K b))
    (op : GateOp) (args : List (Wire α)) (h : ∀ a ∈ args, Good w a)
    (ok : op = .and ∨ op = .or ∨ op = .not) (sz : args.length ≤ 2) :
    Effect w (if op.eval [false] then 0 else if args.length = 2 then 1 else 0) (Eval op args) args := by
  have zero (z : Wire α) (hz : Good w z) (st : (∀ v ∈ args, Stable v) → Stable z) :
      Effect w 0 z args := ⟨0,w,.nil,le_rfl,hz,fun _ => st⟩
  rcases ok with rfl | rfl | rfl
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .and [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .and [a,b] = conj a b := by simp [Eval,GateOp.eval,conj]; rfl
        rw [eq]
        exact bin w base a b (h a (by simp)) (h b (by simp))
  · cases args with
    | nil => exact zero _ (base false) (fun _ => Or.inl ⟨false,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .or [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .or [a,b] = disj a b := by simp [Eval,GateOp.eval,disj,conj,neg]; funext x; simp [inv,meet]
        rw [eq]
        obtain ⟨c,t,r,k,g,st⟩ := bin w base (neg a) (neg b) (goodNeg (h a (by simp))) (goodNeg (h b (by simp)))
        refine ⟨c,t,r,k,goodNeg g,fun equal stable => stableNeg (st equal ?_)⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | h'
        · exact stableNeg (stable _ (by simp))
        · have hv := List.mem_singleton.mp h'
          exact hv ▸ stableNeg (stable b (by simp))
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      exact zero (neg a) (goodNeg (h a (by simp))) (fun st => stableNeg (st a (by simp)))

def step {α} (v : List (Wire α)) (g : Gate) : List (Wire α) :=
  v ++ [Eval g.op (g.inputs.map fun i => v.getD i (K false))]

theorem get_property {α} (P : α → Prop) (v : List α) (d : α) (i : ℕ)
    (hd : P d) (h : ∀ z ∈ v, P z) : P (v.getD i d) := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

theorem fold {α} (gs : List Gate) (legal : ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w : List (Signal α)) (base : ∀ b, Good w (K b)) (v : List (Wire α))
    (old : ∀ a ∈ v, Good w a) :
    ∃ k t, Run w k t ∧ k ≤ (gs.map Paid).sum ∧
      (∀ a ∈ gs.foldl step v, Good t a) ∧
      (k = (gs.map Paid).sum → (∀ a ∈ v, Stable a) → ∀ a ∈ gs.foldl step v, Stable a) := by
  induction gs generalizing w v with
  | nil => exact ⟨0,w,.nil,le_rfl,old,fun _ st => st⟩
  | cons g gs ih =>
    let args := g.inputs.map fun i => v.getD i (K false)
    have allg : ∀ z ∈ args, Good w z := by
      intro z mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact get_property _ _ _ _ (base false) old
    have h := gateEffect w base g.op args allg (legal g (by simp)).1 (by simpa [args] using (legal g (by simp)).2)
    obtain ⟨c,t,run,cap,gnew,snew⟩ := h
    have ec : c ≤ Paid g := by simpa only [Paid,args,List.length_map] using cap
    have goodKeep {a} (ok : Good w a) : Good t a := ⟨run.keep _ ok.1,run.keep _ ok.2⟩
    have goodNext : ∀ a ∈ step v g, Good t a := by
      intro a mem
      rcases List.mem_append.mp mem with ov | nv
      · exact goodKeep (old a ov)
      · exact (List.mem_singleton.mp nv) ▸ gnew
    obtain ⟨j,u,tail,limit,done,st⟩ := ih (fun z hz => legal z (List.mem_cons_of_mem g hz))
      t (fun b => goodKeep (base b)) (step v g) goodNext
    refine ⟨c+j,u,run.comp tail,by simpa using Nat.add_le_add ec limit,done,?_⟩
    intro equal previous
    simp only [List.map_cons,List.sum_cons] at equal
    apply st (by omega)
    intro a mem
    rcases List.mem_append.mp mem with ov | nv
    · exact previous a ov
    · apply (List.mem_singleton.mp nv) ▸ snew (by simpa only [args,List.length_map,Paid] using (show c = Paid g by omega))
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact get_property _ _ _ _ (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) previous

def addPair (w : List Bool) (ij : ℕ × ℕ) : List Bool :=
  let z := w.getD ij.1 false && w.getD ij.2 false
  w ++ [z,!z]

theorem Run.program {α} {s w : List (Signal α)} {k} (r : Run s k w) :
    ∃ prog : List (ℕ × ℕ), prog.length = k ∧ ∀ x : α,
      prog.foldl addPair (s.map fun f => f x) = w.map fun f => f x := by
  induction r with
  | nil => exact ⟨[],rfl,fun _ => rfl⟩
  | @gate k w r a b ha hb ih =>
    obtain ⟨p,len,sim⟩ := ih
    obtain ⟨i,hi,ei⟩ := List.getElem_of_mem ha
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hb
    refine ⟨p++[(i,j)],by simp [len],?_⟩
    intro x
    rw [List.foldl_append,sim]
    simp only [List.foldl_cons,List.foldl_nil,addPair,List.map_append,List.map_cons,List.map_nil]
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hj)]
    simp [List.getElem_map,ei,ej,meet,inv]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getMap {α β} (h : α → β) (v : List α) (i : ℕ) (d : α) :
    h (v.getD i d) = (v.map h).getD i (h d) := by
  simp [List.getD,List.getElem?_map,Option.getD_map]

theorem aligns {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (gs : List Gate) (v : List (Wire α)) :
    (gs.foldl step v).map h = gs.foldl boolStep (v.map h) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp only [step,boolStep,List.map_append,List.map_cons,List.map_nil,he,List.map_map,
      Function.comp_def,getMap h,hd]

theorem outputMap {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (C : Circuit) (v : List (Wire α)) :
    h ((C.gates.foldl step v).getD C.output (K false)) = C.eval (v.map h) := by
  rw [getMap h,hd,aligns h hd he]
  rfl

theorem compile (α : Type) (C : Circuit) (hc : FanInTwo C) (s : List (α → Bool))
    (v : List ((α → Bool) × Bool × Bool)) (constants : ∀ b : Bool, (fun _ : α => b) ∈ s)
    (pins : ∀ a ∈ v, a.1 ∈ s ∧ (fun x => !(a.1 x)) ∈ s ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2))
    (varies : ¬ ∃ b : Bool, ∀ x : α, C.eval (v.map fun a => a.1 x) = b)
    (sensitive : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length < (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
      ∀ x : α, (p.foldl (fun w ij =>
        let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) (s.map fun f => f x)).getD o false = C.eval (v.map fun a => a.1 x) := by
  let make := fun a : (α → Bool) × Bool × Bool => Wire.mk a.1 a.2.1 a.2.2
  let a := v.map make
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u ∧ Stable u := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hg,hn,hs⟩ := pins z hz
    exact ⟨⟨hg,hn⟩,hs⟩
  obtain ⟨k,t,run,limit,accepted,stable⟩ :=
    fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a (fun u hu => (old u hu).1)
  let out := (C.gates.foldl step a).getD C.output (K false)
  have values (x : α) : out.f x = C.eval (v.map fun u => u.1 x) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using
      outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a
  have lo : out.lo = C.eval (v.map fun u => u.2.1) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.lo rfl (fun _ _ => rfl) C a
  have hi : out.hi = C.eval (v.map fun u => u.2.2) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.hi rfl (fun _ _ => rfl) C a
  have lt : k < (C.gates.map Paid).sum := by
    by_contra! ge
    have eq := Nat.le_antisymm limit ge
    have impossible : Stable out := get_property _ _ _ _
      (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) (stable eq (fun u hu => (old u hu).2))
    rcases impossible with ⟨b,h⟩ | e
    · exact varies ⟨b,fun x => (values x).symm.trans (h x)⟩
    · exact sensitive (lo.symm.trans (e.trans hi))
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact lt,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

namespace Graph8
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 5 && x 7)

def edges : List ℕ := [0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7]
def posted (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

theorem table : ∀ x, posted x = target8 x := by decide +kernel

def witness : Circuit := ⟨[
  ⟨.or, [0,2]⟩,
  ⟨.and, [0,3]⟩,
  ⟨.and, [1,4]⟩,
  ⟨.or, [1,4]⟩,
  ⟨.and, [5,7]⟩,
  ⟨.or, [5,7]⟩,
  ⟨.or, [6,10]⟩,
  ⟨.or, [8,12]⟩,
  ⟨.or, [9,13]⟩,
  ⟨.and, [11,14]⟩,
  ⟨.and, [15,16]⟩,
  ⟨.or, [17,18]⟩], 19⟩

theorem size : witness.size = 12 := by decide +kernel

theorem legal : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide +kernel

theorem rawValue : ∀ x, circuitFun 8 witness x = target8 x := by decide +kernel

theorem value (x : Fin 8 → Bool) : circuitFun 8 witness x = posted x :=
  (rawValue x).trans (table x).symm

abbrev Input7 := Fin 7 → Bool
def perm8 : Fin 8 → Fin 8 := ![2, 5, 1, 0, 6, 3, 7, 4]
def lift8 (x : Input7) (j : Fin 8) : Bool := Fin.cases false x (perm8 j)
def target7 (x : Input7) := target8 (lift8 x)
def signedStart7 (x : Input7) := [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
def signed7 (p : List (ℕ × ℕ)) (o : ℕ) (x : Input7) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart7 x)).getD o false

theorem pin8 (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 8 C x = target8 x) :
    ∃ p o, p.length < (C.gates.map PetersenSignedSlice.Paid).sum ∧
      ∀ x, signed7 p o x = target7 x := by
  let raw := List.ofFn (fun j : Fin 7 => fun x : Input7 => x j)
  let pool := [(fun _ : Input7 => false), (fun _ : Input7 => true)] ++ raw ++
    raw.map (fun u x => !(u x))
  let proto := fun j : Fin 8 => (fun x : Input7 => (Fin.cases false x j : Bool), decide (j = 2), decide (j = 0 ∨ j = 2))
  let pin := fun j : Fin 8 => proto (perm8 j)
  let v := List.ofFn pin
  have constants (b : Bool) : (fun _ : Input7 => b) ∈ pool := by cases b <;> simp [pool]
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun x => !(a.1 x)) ∈ pool ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    change (proto (perm8 j)).1 ∈ pool ∧ (fun x => !((proto (perm8 j)).1 x)) ∈ pool ∧
      ((∃ b, ∀ x, (proto (perm8 j)).1 x = b) ∨ (proto (perm8 j)).2.1 = (proto (perm8 j)).2.2)
    generalize perm8 j = idx
    refine Fin.cases ?_ (fun i => ?_) idx
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · have pos : (fun x : Input7 => x i) ∈ raw := List.mem_ofFn.mpr ⟨i,rfl⟩
      refine ⟨List.mem_append_left _ (List.mem_append_right _ pos),
        List.mem_append_right _ (List.mem_map_of_mem pos), Or.inr ?_⟩
      simp [proto]
  have slice (x : Input7) : C.eval (v.map fun a => a.1 x) = target7 x := by
    simpa [v, pin, proto, lift8, target7, circuitFun, List.map_ofFn, Function.comp_def] using hit (lift8 x)
  have varies : ¬ ∃ b : Bool, ∀ x : Input7, C.eval (v.map fun a => a.1 x) = b := by
    rintro ⟨b,h⟩
    have first := (slice (fun _ => false)).symm.trans (h _)
    have second := (slice (fun _ => true)).symm.trans (h _)
    exact (by decide +kernel : target7 (fun _ => false) ≠ target7 (fun _ => true)) (first.trans second.symm)
  have diff : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2) := by
    have a := hit (fun j => decide (perm8 j = 2))
    have b := hit (fun j => decide (perm8 j = 0 ∨ perm8 j = 2))
    simp only [v,pin,proto,List.map_ofFn,Function.comp_def,circuitFun] at a b ⊢
    rw [a,b]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input7 C ok pool v constants pins varies diff
  refine ⟨p,o,small,fun x => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart7 x)).getD o false = target7 x
  have start : pool.map (fun u => u x) = signedStart7 x := by
    simp only [pool,raw,signedStart7,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← start]
  exact (eval x).trans (slice x)

abbrev Input6 := Fin 6 → Bool
def lift7 (y : Input6) : Input7 := Fin.cases false y
def target6 (y : Input6) := target7 (lift7 y)
def signedStart6 (y : Input6) := [false,true] ++ List.ofFn y ++ (List.ofFn y).map Bool.not
def signed6 (p : List (ℕ × ℕ)) (o : ℕ) (y : Input6) :=
  (p.foldl PetersenSignedSlice.addPair (signedStart6 y)).getD o false

def progGates : List (ℕ × ℕ) → ℕ → List Gate
  | [], _ => []
  | ij :: rest, n => ⟨.and, [ij.1, ij.2]⟩ :: ⟨.not, [n]⟩ :: progGates rest (n+2)

theorem progGates_fold (p : List (ℕ × ℕ)) : ∀ (n : ℕ) (w : List Bool), w.length = n →
    (progGates p n).foldl PetersenSignedSlice.boolStep w = p.foldl PetersenSignedSlice.addPair w := by
  induction p with
  | nil => intro n w _; rfl
  | cons ij rest ih =>
    intro n w hw
    simp only [progGates, List.foldl_cons]
    have step : PetersenSignedSlice.boolStep (PetersenSignedSlice.boolStep w ⟨.and, [ij.1, ij.2]⟩) ⟨.not, [n]⟩ =
        PetersenSignedSlice.addPair w ij := by
      subst hw
      simp [PetersenSignedSlice.boolStep, PetersenSignedSlice.addPair, GateOp.eval]
    rw [step]
    exact ih (n+2) _ (by simp [PetersenSignedSlice.addPair, hw])

theorem progGates_paid (p : List (ℕ × ℕ)) : ∀ n, ((progGates p n).map PetersenSignedSlice.Paid).sum = p.length := by
  induction p with
  | nil => intro n; rfl
  | cons ij rest ih =>
    intro n
    simp only [progGates, List.map_cons, List.sum_cons, ih, List.length_cons]
    simp [PetersenSignedSlice.Paid, GateOp.eval]
    omega

theorem progGates_fan (p : List (ℕ × ℕ)) : ∀ n o, FanInTwo ⟨progGates p n, o⟩ := by
  induction p with
  | nil => intro n o g hg; simp [progGates] at hg
  | cons ij rest ih =>
    intro n o g hg
    simp only [progGates, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ih (n+2) o g hg

theorem progEval (p : List (ℕ × ℕ)) (o : ℕ) (w : List Bool) (hw : w.length = 16) :
    Circuit.eval ⟨progGates p 16, o⟩ w = (p.foldl PetersenSignedSlice.addPair w).getD o false := by
  change ((progGates p 16).foldl PetersenSignedSlice.boolStep w).getD o false = _
  rw [progGates_fold p 16 w hw]

theorem pin7 (p1 : List (ℕ × ℕ)) (o1 : ℕ) (hit : ∀ x, signed7 p1 o1 x = target7 x) :
    ∃ p o, p.length < p1.length ∧ ∀ y, signed6 p o y = target6 y := by
  let C2 : Circuit := ⟨progGates p1 16, o1⟩
  let raw := List.ofFn (fun j : Fin 6 => fun y : Input6 => y j)
  let pool := [(fun _ : Input6 => false), (fun _ : Input6 => true)] ++ raw ++
    raw.map (fun (u : Input6 → Bool) (y : Input6) => !(u y))
  let pos := fun j : Fin 7 => ((fun y : Input6 => lift7 y j), decide (j = 2), decide (j = 0 ∨ j = 2))
  let negs := fun j : Fin 7 => ((fun y : Input6 => !(lift7 y j)), !decide (j = 2), !decide (j = 0 ∨ j = 2))
  let v := [((fun _ : Input6 => false), false, false), ((fun _ : Input6 => true), true, true)] ++
    List.ofFn pos ++ List.ofFn negs
  have constants (b : Bool) : (fun _ : Input6 => b) ∈ pool := by cases b <;> simp [pool]
  have varIn (i : Fin 6) : (fun y : Input6 => y i) ∈ pool :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have negIn (i : Fin 6) : (fun y : Input6 => !(y i)) ∈ pool :=
    List.mem_append_right _ (List.mem_map_of_mem (f := fun (u : Input6 → Bool) (y : Input6) => !(u y)) (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have pins : ∀ a ∈ v, a.1 ∈ pool ∧ (fun y => !(a.1 y)) ∈ pool ∧
      ((∃ b, ∀ y, a.1 y = b) ∨ a.2.1 = a.2.2) := by
    intro a ha
    simp only [v, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ((rfl | rfl) | ha) | ha
    · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
    · exact ⟨constants true, constants false, Or.inl ⟨true, fun _ => rfl⟩⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · exact ⟨constants false, constants true, Or.inl ⟨false, fun _ => rfl⟩⟩
      · refine ⟨varIn i, negIn i, Or.inr ?_⟩
        simp [pos]
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
      · exact ⟨constants true, constants false, Or.inl ⟨true, fun _ => rfl⟩⟩
      · have e : (fun y : Input6 => !!(lift7 y i.succ)) = (fun y => y i) := by
          funext y
          simp [lift7]
        refine ⟨negIn i, ?_, Or.inr ?_⟩
        · show (fun y : Input6 => !!(lift7 y i.succ)) ∈ pool
          rw [e]
          exact varIn i
        · simp [negs]
  have evalC (x : Input7) : C2.eval (signedStart7 x) = target7 x := by
    rw [progEval p1 o1 _ (by simp [signedStart7])]
    exact hit x
  have start (y : Input6) : v.map (fun a => a.1 y) = signedStart7 (lift7 y) := by
    simp only [v, pos, negs, signedStart7, List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
      Function.comp_def]
  have startLo : v.map (fun a => a.2.1) = signedStart7 (fun j => decide (j = 2)) := by
    simp only [v, pos, negs, signedStart7, List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
      Function.comp_def]
  have startHi : v.map (fun a => a.2.2) = signedStart7 (fun j => decide (j = 0 ∨ j = 2)) := by
    simp only [v, pos, negs, signedStart7, List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
      Function.comp_def]
  have varies : ¬ ∃ b : Bool, ∀ y : Input6, C2.eval (v.map fun a => a.1 y) = b := by
    rintro ⟨b,h⟩
    have first := h (fun _ => false)
    have second := h (fun _ => true)
    rw [start, evalC] at first second
    exact (by decide +kernel : target6 (fun _ => false) ≠ target6 (fun _ => true)) (first.trans second.symm)
  have diff : C2.eval (v.map fun a => a.2.1) ≠ C2.eval (v.map fun a => a.2.2) := by
    rw [startLo, startHi, evalC, evalC]
    decide +kernel
  obtain ⟨p,o,small,eval⟩ := PetersenSignedSlice.compile Input6 C2 (progGates_fan p1 16 o1) pool v
    constants pins varies diff
  have paidEq : (C2.gates.map PetersenSignedSlice.Paid).sum = p1.length := progGates_paid p1 16
  have small' : p.length < (C2.gates.map PetersenSignedSlice.Paid).sum := small
  refine ⟨p,o,by omega,fun y => ?_⟩
  change (p.foldl PetersenSignedSlice.addPair (signedStart6 y)).getD o false = target6 y
  have s6 : pool.map (fun u => u y) = signedStart6 y := by
    simp only [pool,raw,signedStart6,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  rw [← s6]
  exact (eval y).trans ((congrArg C2.eval (start y)).trans (evalC (lift7 y)))

end Graph8

namespace SignedFrontier

abbrev W := BitVec 64

def canonical (w : W) : W := if w.getLsbD 0 then ~~~w else w

def choices (a b : W) : List W :=
  [a &&& b, a &&& ~~~b, ~~~a &&& b, a ||| b]

theorem canonical_not (w : W) : canonical (~~~w) = canonical w := by
  cases h : w.getLsbD 0 <;> simp_all [canonical, BitVec.not_not]

theorem canonical_bit (w : W) : (canonical w).getLsbD 0 = false := by
  unfold canonical
  split <;> simp_all

theorem operation (a b : W) :
    canonical (a &&& b) ∈ choices (canonical a) (canonical b) := by
  cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
    simp_all [choices, canonical, BitVec.not_and, BitVec.not_not]

theorem constants (a b : W) (h : a = 0 ∨ b = 0 ∨ a = b) :
    ∀ w ∈ choices a b, w = 0 ∨ w = a ∨ w = b := by
  rcases h with rfl | rfl | rfl <;> simp [choices]
  · exact Or.inr BitVec.allOnes_and
  · exact Or.inr (Or.inl BitVec.and_allOnes)

inductive Cone (goal : W) : ℕ → Finset W → Prop where
  | done : Cone goal 0 {goal}
  | step {k : ℕ} {needed : Finset W} {a b w : W}
      (rest : Cone goal k needed) (wanted : w ∈ needed)
      (a0 : a ≠ 0) (b0 : b ≠ 0) (ab : a ≠ b) (aw : a ≠ w) (bw : b ≠ w)
      (form : w ∈ choices a b) :
      Cone goal (k+1) (insert a (insert b (needed.erase w)))

theorem Cone.size {goal : W} {k : ℕ} {s : Finset W} (h : Cone goal k s) :
    s.card ≤ k+1 := by
  induction h with
  | done => simp
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    have e := Finset.card_erase_of_mem wanted
    have hn := Finset.card_pos.mpr ⟨w,wanted⟩
    have p := Finset.card_insert_le b (needed.erase w)
    have q := Finset.card_insert_le a (insert b (needed.erase w))
    omega

def add (ws : List W) (ij : ℕ × ℕ) : List W :=
  let w := ws.getD ij.1 0 &&& ws.getD ij.2 0
  ws ++ [w,~~~w]

def available (ws : List W) : Finset W := insert 0 (ws.map canonical).toFinset

theorem available_read (ws : List W) (i : ℕ) : canonical (ws.getD i 0) ∈ available ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp only [available, Finset.mem_insert, List.mem_toFinset, List.mem_map]
    exact Or.inr ⟨_,List.getElem_mem hi,rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [available,canonical]

theorem available_add (ws : List W) (ij : ℕ × ℕ) :
    available (add ws ij) = insert (canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)) (available ws) := by
  ext w
  simp [available,add,canonical_not]
  tauto

theorem extract (p : List (ℕ × ℕ)) (ws : List W) (g : W) (k : ℕ) (s : Finset W)
    (h : Cone g k s) (hs : s ⊆ available (p.foldl add ws)) :
    ∃ j t, j ≤ k+p.length ∧ t ⊆ available ws ∧ Cone g j t := by
  induction p generalizing ws k s with
  | nil => exact ⟨k,s,by simp,hs,h⟩
  | cons ij tail ih =>
    obtain ⟨j,t,hj,ht,hr⟩ := ih (add ws ij) k s h hs
    rw [available_add] at ht
    by_cases sub : t ⊆ available ws
    · exact ⟨j,t,by simp only [List.length_cons]; omega,sub,hr⟩
    · let a := canonical (ws.getD ij.1 0)
      let b := canonical (ws.getD ij.2 0)
      let w := canonical (ws.getD ij.1 0 &&& ws.getD ij.2 0)
      have ha : a ∈ available ws := available_read _ _
      have hb : b ∈ available ws := available_read _ _
      have hz : (0 : W) ∈ available ws := Finset.mem_insert_self ..
      have new : w ∉ available ws := by
        intro hold
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).elim (fun e => e ▸ hold) id)
      have want : w ∈ t := by
        by_contra hn
        exact sub (fun z h' => (Finset.mem_insert.mp (ht h')).resolve_left (by rintro rfl; contradiction))
      have form : w ∈ choices a b := operation _ _
      have diff : ¬ (a = 0 ∨ b = 0 ∨ a = b) := by
        intro bad
        rcases constants a b bad w form with e | e | e <;> apply new <;> simp_all
      refine ⟨j+1,_,by simp only [List.length_cons]; omega,?_,
        Cone.step hr want (fun e => diff (Or.inl e)) (fun e => diff (Or.inr (Or.inl e)))
          (fun e => diff (Or.inr (Or.inr e))) (fun e => new (e ▸ ha)) (fun e => new (e ▸ hb)) form⟩
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact ha
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact hb
      obtain ⟨hne,hzt⟩ := Finset.mem_erase.mp hz'
      exact (Finset.mem_insert.mp (ht hzt)).resolve_left hne

theorem Cone.noZero {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (hg : g ≠ 0) :
    0 ∉ s := by
  induction h with
  | done => exact fun hz => hg (Finset.mem_singleton.mp hz).symm
  | step rest wanted a0 b0 ab aw bw form ih =>
    intro hz
    rcases Finset.mem_insert.mp hz with e | hm
    · exact a0 e.symm
    rcases Finset.mem_insert.mp hm with e | hm
    · exact b0 e.symm
    exact ih (Finset.mem_of_mem_erase hm)

theorem same_choice (a b w : W) (hw : w ∈ choices a b) (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    w.getLsbD i = w.getLsbD j := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,hi,hj,decide_true,
      Bool.true_and,ha,hb]

theorem Cone.agree {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s)
    (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (same : ∀ u ∈ s, u.getLsbD i = u.getLsbD j) : g.getLsbD i = g.getLsbD j := by
  induction h with
  | done => exact same _ (Finset.mem_singleton_self _)
  | @step k needed a b w rest wanted a0 b0 ab aw bw form ih =>
    apply ih
    intro u hu
    by_cases h : u = w
    · subst u
      exact same_choice _ _ _ form i j hi hj (same a (by simp)) (same b (by simp))
    · exact same u (by simp [h, hu])

def rowMask (r : ℕ) (u : W) := if u.getLsbD r then u else ~~~u

def survivors (r : ℕ) : List W → W → W
  | [], mask => mask
  | a :: tail, mask =>
    if mask = 0 then 0 else survivors r tail (mask &&& rowMask r a)

theorem survivor_sound (r j : ℕ) (hj : j < 64) (s : List W) (m : W)
    (hit : (survivors r s m).getLsbD j = true) :
    m.getLsbD j = true ∧ ∀ u ∈ s, u.getLsbD r = u.getLsbD j := by
  induction s generalizing m with
  | nil => exact ⟨hit,by simp⟩
  | cons a tail ih =>
    simp only [survivors] at hit
    split at hit
    · simp at hit
    · obtain ⟨head,rest⟩ := ih _ hit
      simp only [BitVec.getLsbD_and,Bool.and_eq_true] at head
      refine ⟨head.1,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | h
      · have v := head.2
        unfold rowMask at v
        cases h : u.getLsbD r <;> simp_all
      · exact rest u h

def covered (g : W) (rows : List ℕ) (s : List W) :=
  rows.all fun r => survivors r s g == 0

theorem Cone.covered {g : W} {k : ℕ} {s : List W} (h : Cone g k s.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) :
    covered g rows s = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨limit,off⟩ := neg r hr
  cases hv : (survivors r s g).getLsbD j with
  | false => simp
  | true =>
    obtain ⟨on,same⟩ := survivor_sound r j hj s g hv
    have eq := h.agree r j limit hj (by simpa using same)
    simp [off,on] at eq

def withWire (keep : Bool) (a : W) (s : List W) := if keep then a :: s else s

theorem mem_withWire {u a : W} {s : List W} (keep : Bool) :
    u ∈ withWire keep a s ↔ (keep = true ∧ u = a) ∨ u ∈ s := by
  cases keep <;> simp [withWire]

def after (s : List W) (a b w : W) (ka kb : Bool) : List W :=
  w :: withWire ka a (withWire kb b (s.filter fun u => u != a && u != b))

theorem after_exact (s : List W) (needed : Finset W) (a b w : W)
    (hs : s.toFinset = insert a (insert b (needed.erase w))) (want : w ∈ needed) :
    (after s a b w (decide (a ∈ needed)) (decide (b ∈ needed))).toFinset = needed := by
  ext u
  have mem : u ∈ s ↔ u = a ∨ u = b ∨ u ≠ w ∧ u ∈ needed := by
    rw [← List.mem_toFinset,hs]
    simp
  simp only [List.mem_toFinset,after,List.mem_cons,mem_withWire,decide_eq_true_eq,
    List.mem_filter,Bool.and_eq_true,bne_iff_ne,mem]
  grind

def onePair (s : List W) (f : List W → Bool) (a b : W) :=
  (choices a b).any fun w => w != 0 && !s.contains w &&
    ([false,true] : List Bool).any fun ka => ([false,true] : List Bool).any fun kb =>
      f (after s a b w ka kb)

def moves (s : List W) (f : List W → Bool) :=
  s.any fun a => s.any fun b => decide (a.toNat < b.toNat) && onePair s f a b

theorem swap_choices {a b w : W} : w ∈ choices a b → w ∈ choices b a := by
  simp only [choices,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with rfl | rfl | rfl | rfl <;> simp [BitVec.and_comm,BitVec.or_comm]

theorem after_nodup (s : List W) (hs : s.Nodup) (a b w : W) (ka kb : Bool)
    (diff : a ≠ b) (fresh : w ∉ s) (aw : a ≠ w) (bw : b ≠ w) :
    (after s a b w ka kb).Nodup := by
  have base := hs.filter (fun u => u != a && u != b)
  have ha : a ∉ s.filter (fun u => u != a && u != b) := by simp
  have hb : b ∉ s.filter (fun u => u != a && u != b) := by simp
  have hw : w ∉ s.filter (fun u => u != a && u != b) := by simp [fresh]
  cases ka <;> cases kb <;> simp [after,withWire,base,fresh,Ne.symm aw,Ne.symm bw,diff]

theorem onePair_complete (s : List W) (f : List W → Bool)
    {g a b w : W} {k : ℕ} {needed : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (ab : a ≠ b) (rest : Cone g k needed) (want : w ∈ needed)
    (hs : s.toFinset = insert a (insert b (needed.erase w)))
    (aw : a ≠ w) (bw : b ≠ w) (form : w ∈ choices a b)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    onePair s f a b = true := by
  have nz : w ≠ 0 := fun e => rest.noZero hg (e ▸ want)
  have fresh : w ∉ s := by
    rw [← List.mem_toFinset,hs]
    simp [Ne.symm aw,Ne.symm bw]
  apply List.any_eq_true.mpr
  refine ⟨w,form,?_⟩
  simp only [bne_iff_ne.mpr nz,List.contains_eq_mem,decide_eq_false fresh,
    Bool.not_false,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨decide (a ∈ needed),by cases decide (a ∈ needed) <;> simp,?_⟩
  apply List.any_eq_true.mpr
  refine ⟨decide (b ∈ needed),by cases decide (b ∈ needed) <;> simp,?_⟩
  exact succ _ (after_nodup s unique a b w _ _ ab fresh aw bw) ((after_exact s needed a b w hs want).symm ▸ rest)

theorem moves_complete (s : List W) (f : List W → Bool)
    {g : W} {k : ℕ} {state : Finset W} (hg : g ≠ 0)
    (unique : s.Nodup) (h : Cone g (k+1) state) (eq : s.toFinset = state)
    (succ : ∀ t : List W, t.Nodup → Cone g k t.toFinset → f t = true) :
    moves s f = true := by
  cases h with
  | @step _ needed a b w rest want a0 b0 ab aw bw form =>
    have ha : a ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_self ..)
    have hb : b ∈ s := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    apply List.any_eq_true.mpr
    have distinct : a.toNat ≠ b.toNat := fun e => ab (BitVec.eq_of_toNat_eq e)
    rcases lt_or_gt_of_ne distinct with lt | gt
    · refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
      simp only [lt,decide_true,Bool.true_and]
      exact onePair_complete s f hg unique ab rest want eq aw bw form succ
    · refine ⟨b,hb,List.any_eq_true.mpr ⟨a,ha,?_⟩⟩
      simp only [gt,decide_true,Bool.true_and]
      rw [Finset.insert_comm] at eq
      exact onePair_complete s f hg unique ab.symm rest want eq bw aw (swap_choices form) succ

def feasible (g : W) (rows : List ℕ) : ℕ → List W → Bool
  | 0, s => s.contains g
  | k+1, s => s.contains g ||
    (decide (s.length ≤ k+2) && covered g rows s &&
      moves s (feasible g rows k))

theorem feasible_complete {g : W} (hg : g ≠ 0) (rows : List ℕ)
    (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false)
    (cap : ℕ) (s : List W) (unique : s.Nodup) (k : ℕ) (bound : k ≤ cap) (h : Cone g k s.toFinset) :
    feasible g rows cap s = true := by
  induction cap generalizing k s with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
    simpa [feasible] using final h
  | succ cap ih =>
    simp only [feasible,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    cases k with
    | zero =>
      left
      have final {t : Finset W} (c : Cone g 0 t) : g ∈ t := by cases c; simp
      simpa using final h
    | succ k =>
      right
      refine ⟨⟨by have sz := h.size; rw [List.toFinset_card_of_nodup unique] at sz; omega,h.covered rows neg⟩,?_⟩
      exact moves_complete _ _ hg unique h rfl (fun t nd ht => ih t nd k (by omega) ht)

def Essential (g : W) (raws : List W) :=
  ∀ w ∈ raws, ∃ i j : Fin 64, g.getLsbD i.val ≠ g.getLsbD j.val ∧
    ∀ v ∈ raws, v ≠ w → v.getLsbD i.val = v.getLsbD j.val

theorem Cone.initial {g : W} (hg : g ≠ 0) (raws : List W) (ess : Essential g raws)
    {k : ℕ} {s : Finset W} (h : Cone g k s) (sub : s ⊆ insert 0 raws.toFinset) :
    s = raws.toFinset := by
  have contained : s ⊆ raws.toFinset := by
    intro z hz
    exact (Finset.mem_insert.mp (sub hz)).resolve_left (fun e => h.noZero hg (e ▸ hz))
  apply Finset.Subset.antisymm contained
  intro w hw
  by_contra missing
  obtain ⟨i,j,diff,others⟩ := ess w (List.mem_toFinset.mp hw)
  exact diff (h.agree _ _ i.isLt j.isLt (fun u hu =>
    others u (List.mem_toFinset.mp (contained hu)) (fun e => missing (e ▸ hu))))

def evaluate (p : List (ℕ × ℕ)) (ws : List W) (o : ℕ) : W := (p.foldl add ws).getD o 0

theorem from_check (g : W) (hg : g ≠ 0) (raws ws : List W) (unique : raws.Nodup) (start : available ws = insert 0 raws.toFinset)
    (rows : List ℕ) (neg : ∀ r ∈ rows, r < 64 ∧ g.getLsbD r = false) (ess : Essential g raws)
    (cap : ℕ) (checked : feasible g rows cap raws = false) (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : canonical (evaluate p ws o) = g) : cap < p.length := by
  by_contra! short
  have sub : {g} ⊆ available (p.foldl add ws) := by
    apply Finset.singleton_subset_iff.mpr
    rw [← hit]
    exact available_read _ _
  obtain ⟨k,s,bound,inside,run⟩ := extract p ws g 0 {g} Cone.done sub
  rw [start] at inside
  have eq := run.initial hg raws ess inside
  rw [eq] at run
  have possible := feasible_complete hg rows neg cap raws unique k (by omega) run
  simp [checked] at possible

structure Switch where
  distance : ℕ
  low : W
  high : W

def Switch.source (s : Switch) (r : ℕ) :=
  if s.low.getLsbD r then s.distance + r else if s.high.getLsbD r then r-s.distance else r

def Switch.apply (s : Switch) (w : W) : W :=
  (w &&& ~~~(s.low ||| s.high)) ||| ((w >>> s.distance) &&& s.low) |||
    ((w <<< s.distance) &&& s.high)

def Switch.Valid (s : Switch) :=
  ∀ r : Fin 64, ¬ (s.low.getLsbD r.val = true ∧ s.high.getLsbD r.val = true) ∧
    (s.high.getLsbD r.val = true → s.distance ≤ r.val) ∧
    s.source r.val < 64 ∧ s.source (s.source r.val) = r.val

theorem Switch.read (s : Switch) (ok : s.Valid) (w : W) (r : ℕ) (hr : r < 64) :
    (s.apply w).getLsbD r = w.getLsbD (s.source r) := by
  obtain ⟨disj,lower,_,_⟩ := ok ⟨r,hr⟩
  change ¬ (s.low.getLsbD r = true ∧ s.high.getLsbD r = true) at disj
  change s.high.getLsbD r = true → s.distance ≤ r at lower
  simp only [Switch.apply, BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hr,decide_true,Bool.true_and,Switch.source]
  cases a : s.low.getLsbD r <;> cases b : s.high.getLsbD r <;> simp_all

theorem Switch.inj (s : Switch) (ok : s.Valid) : Function.Injective s.apply := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  obtain ⟨_,_,lim,inv⟩ := ok ⟨r,hr⟩
  have e := congrArg (fun u : W => u.getLsbD (s.source r)) h
  simpa only [s.read ok _ _ lim, inv] using e

theorem Switch.not (s : Switch) (ok : s.Valid) (w : W) : s.apply (~~~w) = ~~~(s.apply w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound := (ok ⟨i,hi⟩).2.2.1
  simp only [s.read ok _ _ hi,BitVec.getLsbD_not,hi,bound,decide_true,Bool.true_and]

theorem Switch.and (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a &&& b) = s.apply a &&& s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_and]

theorem Switch.or (s : Switch) (ok : s.Valid) (a b : W) :
    s.apply (a ||| b) = s.apply a ||| s.apply b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [s.read ok _ _ hi,BitVec.getLsbD_or]

theorem Cone.switched {g : W} {k : ℕ} {xs : Finset W} (h : Cone g k xs) (s : Switch) (ok : s.Valid) :
    Cone (s.apply g) k (xs.image s.apply) := by
  have zero : s.apply 0 = 0 := by simp [Switch.apply]
  have inj := s.inj ok
  induction h with
  | done => simpa using (Cone.done (goal := s.apply g))
  | @step k ys a b w rest want a0 b0 ab aw bw form ih =>
    have wanted : s.apply w ∈ ys.image s.apply := Finset.mem_image_of_mem _ want
    have erase : (ys.erase w).image s.apply = (ys.image s.apply).erase (s.apply w) := by
      ext x
      simp only [Finset.mem_image,Finset.mem_erase]
      constructor
      · rintro ⟨v,⟨hne,mem⟩,rfl⟩
        exact ⟨fun e => hne (inj e),v,mem,rfl⟩
      · rintro ⟨hne,v,mem,rfl⟩
        exact ⟨v,⟨fun e => hne (congrArg _ e),mem⟩,rfl⟩
    have operate : s.apply w ∈ choices (s.apply a) (s.apply b) := by
      simp only [choices,List.mem_cons,List.not_mem_nil,or_false] at form ⊢
      rcases form with rfl | rfl | rfl | rfl <;> simp [s.and ok,s.or ok,s.not ok]
    simp only [Finset.image_insert,erase]
    exact Cone.step ih wanted (fun e => a0 (inj (e.trans zero.symm)))
      (fun e => b0 (inj (e.trans zero.symm))) (fun e => ab (inj e))
      (fun e => aw (inj e)) (fun e => bw (inj e)) operate

def reindex : List Switch → W → W
  | [], w => w
  | s :: tail, w => reindex tail (s.apply w)

theorem Cone.reindex {g : W} {k : ℕ} {s : Finset W} (h : Cone g k s) (ops : List Switch)
    (ok : ∀ op ∈ ops, op.Valid) :
    Cone (reindex ops g) k (s.image (reindex ops)) := by
  induction ops generalizing s g with
  | nil => simpa [SignedFrontier.reindex] using h
  | cons op tail ih =>
    have step := h.switched op (ok _ List.mem_cons_self)
    have result := ih step (fun u hu => ok u (List.mem_cons_of_mem _ hu))
    simpa only [SignedFrontier.reindex,Finset.image_image,Function.comp_def] using result

def found (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) (k : ℕ) (s : List W) :=
  let (i,j) := lookup k s
  decide (i < count k) && (s.map (reindex (sym j))).isPerm (words k i)

def closed (g : W) (negative : List ℕ) (words : ℕ → ℕ → List W) (count : ℕ → ℕ)
    (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) : ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    !s.contains g && !(moves s fun t =>
      t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) && covered g negative t &&
        !found words count lookup sym k t))

theorem closed_excludes (g : W) (hg : g ≠ 0) (negative : List ℕ)
    (neg : ∀ r ∈ negative, r < 64 ∧ g.getLsbD r = false)
    (words : ℕ → ℕ → List W) (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ)
    (sym : ℕ → List Switch) (valid : ∀ j, ∀ op ∈ sym j, op.Valid)
    (fix : ∀ j, reindex (sym j) g = g) (cap : ℕ)
    (nd : ∀ k ≤ cap, ∀ i < count k, (words k i).Nodup)
    (checks : ∀ k ≤ cap, ∀ i < count k, closed g negative words count lookup sym k i = true) :
    ∀ k ≤ cap, ∀ i < count k, ∀ d ≤ k, ¬ Cone g d (words k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi d hd run
    have de : d = 0 := by omega
    subst d
    have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
    have mem := List.mem_toFinset.mp (terminal run)
    simpa [closed,mem] using checks 0 hk i hi
  | succ k ih =>
    intro hk i hi d hd run
    obtain ⟨absent,reject⟩ := Bool.and_eq_true_iff.mp (checks (k+1) hk i hi)
    cases d with
    | zero =>
      have terminal {t : Finset W} (p : Cone g 0 t) : g ∈ t := by cases p; simp
      have mem := List.mem_toFinset.mp (terminal run)
      simp [mem] at absent
    | succ d =>
      let test := fun t : List W => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
        covered g negative t && !found words count lookup sym k t)
      have next := moves_complete (words (k+1) i) test hg (nd _ hk _ hi) run rfl (fun t uniq ht => by
        dsimp only [test]
        by_cases mem : g ∈ t
        · simp [mem]
        have positive : 0 < k := by
          by_contra! fail
          have dz : d = 0 := by omega
          subst d
          have terminal {u : Finset W} (p : Cone g 0 u) : g ∈ u := by cases p; simp
          exact mem (List.mem_toFinset.mp (terminal ht))
        have size := ht.size
        rw [List.toFinset_card_of_nodup uniq] at size
        have no : found words count lookup sym k t = false := by
          by_contra! yes
          have hfound : found words count lookup sym k t = true := by simpa using yes
          obtain ⟨inside,perm⟩ := Bool.and_eq_true_iff.mp hfound
          have hree := ht.reindex (sym (lookup k t).2) (valid _)
          rw [fix] at hree
          have eq : (t.map (reindex (sym (lookup k t).2))).toFinset = (words k (lookup k t).1).toFinset := by
            ext v
            simp only [List.mem_toFinset]
            exact (List.isPerm_iff.mp perm).mem_iff
          have into : t.toFinset.image (reindex (sym (lookup k t).2)) = (words k (lookup k t).1).toFinset := by
            rw [← eq]
            ext v
            simp
          rw [into] at hree
          exact ih (by omega) _ (of_decide_eq_true inside) d (by omega) hree
        simp [positive,show t.length ≤ k+1 by omega,ht.covered negative neg,no])
      change (!moves (words (k+1) i) test) = true at reject
      simp [next] at reject

end SignedFrontier

namespace SignedFrontier

theorem zero_inter (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and

theorem survivors_zero (r : ℕ) (s : List W) : survivors r s 0 = 0 := by
  cases s <;> simp [survivors]

theorem survivors_inter (r : ℕ) (s : List W) (u v : W) :
    survivors r s (u &&& v) = survivors r s u &&& v := by
  induction s generalizing u with
  | nil => rfl
  | cons a tail ih =>
    by_cases hu : u = 0
    · subst u
      rw [zero_inter, survivors_zero, zero_inter]
    · by_cases hv : u &&& v = 0
      · rw [hv, survivors_zero, survivors, if_neg hu]
        rw [← ih]
        rw [BitVec.and_assoc, BitVec.and_comm (rowMask r a), ← BitVec.and_assoc, hv]
        rw [zero_inter, survivors_zero]
      · rw [survivors, if_neg hv, survivors, if_neg hu, ← ih]
        rw [BitVec.and_assoc, BitVec.and_comm v, ← BitVec.and_assoc]

def screen (g : W) (base : List W) : List ℕ → List W → List W
  | [], candidates => candidates
  | r :: rows, candidates =>
    if candidates.isEmpty then [] else
    let mask := survivors r base g
    if mask = 0 then screen g base rows candidates else
      screen g base rows (candidates.filter fun w => (mask &&& rowMask r w) == 0)

theorem screen_keeps {g w : W} (hg : g ≠ 0) (base : List W) (rows : List ℕ)
    (candidates : List W) (hw : w ∈ candidates) (ok : covered g rows (w :: base) = true) :
    w ∈ screen g base rows candidates := by
  induction rows generalizing candidates with
  | nil => exact hw
  | cons r rows ih =>
    have clear := List.all_eq_true.mp ok r List.mem_cons_self
    have tail : covered g rows (w :: base) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      exact List.all_eq_true.mp ok i (List.mem_cons_of_mem _ hi)
    have hm : survivors r base g &&& rowMask r w = 0 := by
      have h := beq_iff_eq.mp clear
      simpa only [survivors, if_neg hg, survivors_inter] using h
    unfold screen
    have hn : candidates.isEmpty = false := by
      cases candidates <;> simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ih _ hw tail
    · exact ih _ (List.mem_filter.mpr ⟨hw,beq_iff_eq.mpr hm⟩) tail

def fastBranch (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (candidates base : List W) : Bool :=
  decide (0 < k) && decide (base.length ≤ k) &&
    (screen g base rows candidates).any fun w => !locate (w :: base)

def fastPair (g : W) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) : Bool :=
  let choices' := choices a b
  choices'.contains g ||
    let rest := s.filter fun u => u != a && u != b
    let fresh := choices'.filter fun w => w != 0 && !s.contains w
    fastBranch g rows locate k fresh rest ||
    fastBranch g rows locate k fresh (a :: rest) ||
    fastBranch g rows locate k fresh (b :: rest) ||
    fastBranch g rows locate k fresh (a :: b :: rest)

def fastClosed (g : W) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch) :
    ℕ → ℕ → Bool
  | 0, i => !(words 0 i).contains g
  | k+1, i =>
    let s := words (k+1) i
    let locate := found words count lookup sym k
    !s.contains g && !(s.any fun a => s.any fun b =>
      decide (a.toNat < b.toNat) && fastPair g rows locate k s a b)

theorem branch_of {g w : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (fresh base : List W) (hw : w ∈ fresh)
    (hk : 0 < k) (len : (w :: base).length ≤ k+1)
    (cov : covered g rows (w :: base) = true) (miss : locate (w :: base) = false) :
    fastBranch g rows locate k fresh base = true := by
  have p : base.length ≤ k := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using len
  simp only [fastBranch, hk, p, decide_true, Bool.true_and]
  exact List.any_eq_true.mpr ⟨w, screen_keeps hg base rows fresh hw cov, by simp [miss]⟩

theorem fastPair_of {g : W} (hg : g ≠ 0) (rows : List ℕ) (locate : List W → Bool)
    (k : ℕ) (s : List W) (a b : W) (ha : a ∈ s) (hb : b ∈ s) (absent : g ∉ s)
    (h : onePair s (fun t => t.contains g || (decide (0 < k) && decide (t.length ≤ k+1) &&
      covered g rows t && !locate t)) a b = true) :
    fastPair g rows locate k s a b = true := by
  obtain ⟨w,form,test⟩ := List.any_eq_true.mp h
  obtain ⟨fresh,keeps⟩ := Bool.and_eq_true_iff.mp test
  obtain ⟨ka,_,rest⟩ := List.any_eq_true.mp keeps
  obtain ⟨kb,_,ok⟩ := List.any_eq_true.mp rest
  let base := s.filter fun u => u != a && u != b
  have wf : w ∈ (choices a b).filter (fun z => z != 0 && !s.contains z) :=
    List.mem_filter.mpr ⟨form,fresh⟩
  by_cases hit : g ∈ choices a b
  · simp [fastPair,hit]
  · have nw : w ≠ g := fun eq => hit (eq ▸ form)
    have na : g ≠ a := fun e => absent (e ▸ ha)
    have nb : g ≠ b := fun e => absent (e ▸ hb)
    have ng : g ∉ base := by
      intro h
      exact absent (List.mem_filter.mp h).1
    have stop : (after s a b w ka kb).contains g = false := by
      cases ka <;> cases kb <;>
        simp [after,withWire,List.contains_eq_mem,Ne.symm nw,na,nb,absent]
    dsimp only at ok
    rw [stop, Bool.false_or] at ok
    obtain ⟨left,miss⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨dims,cov⟩ := Bool.and_eq_true_iff.mp left
    obtain ⟨positive,len⟩ := Bool.and_eq_true_iff.mp dims
    have hk := of_decide_eq_true positive
    have hl := of_decide_eq_true len
    have hm : locate (after s a b w ka kb) = false := by simpa using miss
    have spec := branch_of hg rows locate k _ _ wf hk hl cov hm
    cases ka <;> cases kb <;>
      simp [after,withWire] at spec <;> simp [fastPair, hit, spec]

theorem fastClosed_sound (g : W) (hg : g ≠ 0) (rows : List ℕ) (words : ℕ → ℕ → List W)
    (count : ℕ → ℕ) (lookup : ℕ → List W → ℕ × ℕ) (sym : ℕ → List Switch)
    (k i : ℕ) (ok : fastClosed g rows words count lookup sym k i = true) :
    closed g rows words count lookup sym k i = true := by
  cases k with
  | zero => exact ok
  | succ k =>
    obtain ⟨absent,fast⟩ := Bool.and_eq_true_iff.mp ok
    apply Bool.and_eq_true_iff.mpr
    refine ⟨absent,?_⟩
    have ng : g ∉ words (k+1) i := by simpa [List.contains_eq_mem] using absent
    by_contra! fail
    have h : moves (words (k+1) i) (fun t => t.contains g || (decide (0 < k) &&
        decide (t.length ≤ k+1) && covered g rows t &&
        !found words count lookup sym k t)) = true := by simpa using fail
    obtain ⟨a,ha,inside⟩ := List.any_eq_true.mp h
    obtain ⟨b,hb,both⟩ := List.any_eq_true.mp inside
    obtain ⟨lt,slow⟩ := Bool.and_eq_true_iff.mp both
    have fp := fastPair_of hg rows (found words count lookup sym k) k _ a b ha hb ng slow
    have yes : ((words (k+1) i).any fun a => (words (k+1) i).any fun b =>
        decide (a.toNat < b.toNat) && fastPair g rows (found words count lookup sym k) k
          (words (k+1) i) a b) = true :=
      List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨lt,fp⟩⟩⟩
    simp [yes] at fast

end SignedFrontier

namespace SignedFrontier.SmallCert

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_member {f n o} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    intro i lo hi
    obtain ⟨first,tail⟩ := Bool.and_eq_true_iff.mp h
    rcases Nat.eq_or_lt_of_le lo with rfl | gt
    · exact first
    · exact ih tail i (by omega) (by omega)

theorem span_join {f a o b} (left : span f a o = true) (right : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using right
  | succ a ih =>
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp left
    rw [Nat.succ_add]
    exact Bool.and_eq_true_iff.mpr ⟨first,ih rest (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right)⟩

end SignedFrontier.SmallCert

namespace SignedFrontier.SmallCert.Tri

def raw : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : W := 0xffffffe8ffe8e8e8
def negative : List Nat := [0, 1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 32, 33, 34, 36]
theorem nonzero : target ≠ 0 := by decide +kernel
theorem neg : ∀ r ∈ negative, r < 64 ∧ target.getLsbD r = false := by
  intro r hr
  simp only [negative,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem essential : Essential target raw := by
  intro w hw
  simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨2,3,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,3,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨1,5,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨16,24,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨8,24,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  · refine ⟨8,40,by decide +kernel,?_⟩
    intro u hu distinct
    simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel

def dictionary (k page : ℕ) : ℕ :=
  match k with
  | 0 => if page < 1 then 0xa0a0a0a0a0a0a0a000000000ffffff000000ffffffff0000ffffffff000088888888aaaaaaaaaaaaffffffff0f000000aa00ff00ff00ff00ffffffff880088000a0aaaaaaaaaaaaaffffffffaa0000000f00ff00ff00ff00ffff8888ffff88880000cccccccccccceaeaeaeaeaeaeaeaffffffff08080808aa00aaaaaaaaaaaaffffffff8080808000aaaaaaaaaaaaaafffff0f0f0f0f0f00000ff00ff00ff00f8f8f8f8f8f8f8f8ffffffffff00ff00eeeeeeeeeeeeeeeeffffff000000ff0000000000ff00ff00ff000000ff000000ffffffff88888888fcfcfcfcfcfcfcfcff00ff00ff000000ffffff000000000000000000ff000000e8e8e8e8e8e8e8e8ffffffffff000000ffff0000000000000000ff00ff000000c8c8c8c8c8c8c8c8ffffff00ffff00000000000000ffff00ffffff00ffffff00000000000000ff00ffffffff00000000ffff0000ffff0000e0e0e0e0e0e0e0e0ffffffffffff0000ffffff00ff00ff00ffffffffe0e0e0e0ffffe0e0ffffe0e08888888888888888fff0fff0fff0f0f0000000aaaaaaaaaaffffffffc0c0c0c0ffffc0c0ffffc0c0ff00ff00ff00ff00a8a8a8a8a8a8a8a8fff0f0f0fff0f0f00000aaaaaaaaaaaa000000aa00aaaaaaffffff00ff000000f0f0f0f0f0f0f0f0ccccccccccccccccfffffff0fff0f0f0ffffffccffccccccaaaaaaaaaaaaaaaa0000000000000000 else if page < 2 then 0xffaaffaaaa88aa88aa88aa88ffffffffcccccccc55555555000000000000aaaa0000aaaaffffffffaaaaaaaaafaaafaaafaaafaa88888888aaaaaaaaaaaaaaaaeeeeeeeeaa00aa00ff00ff00ffaaffaaffaaffaaaa00aa00aa00aa00eeaaeeaaeeaaeeaa0a0a0a0aaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaffeeffeeffeeffee000000000000aaaa00000000eeeeeeeeaaaaaa00aaaaaa00fefefefefefefefe00ff00ff00000000aeaeaeaeaeaeaeae8a8a8a8a8a8a8a8aaaaaaaaaffaaffaaaa00aa00aaaaaaaa000000000a0a0a0a00000000aa00aa00ff88ff88ff88ff88000000008888888888008800880088008080808080808080ff00ff00000000000f0f0f0ff0f0f0f000000000ffffffaaaaa8aaa8aaa8aaa8ffffffff000000aaa8a8a8a8aaaaaaaaffffffffa8a8a8a8fafafafafafafafa00000000ffff0000ffff0000ff0000000000ff000000ff00acacacacacacacacc0c0c0c0c0c0c0c0 else 0
  | _ => 0

def encodedPool (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x30201 else 0
  | 3 => if page < 1 then 0x12110b10060f04010605040e0d0c0b0a0609040106050408030604010605040706050401 else 0
  | 4 => if page < 1 then 0x12110b0401280504012712160b1510222605040e17160b200a25160b15100d0c0b24011e23050408220504012117160b20101f1909040114130504081e0504011d17160b1c0a1b13050401060b050401190504011a190605040113050401181306050401000605040117160b15101413050401 else 0
  | 5 => if page < 1 then 0x160b0504014a17160b05044948160b05040117160b05044746160b05040117160b05040e46160b05040a22160b05040e17160b45040a142a19050401221605040127190504014427430b05040127160b0504013e1e050401422717160b04410117160b403f1017160b150110160b0504013d1e0b0504011817160b05151019260504013e17160b2915100017160b1510140b0504013d1e0b0504013d3c160b05040117160b05043b3a160b05040117160504013938160b05040117160b05043736160b05040117160504013525160b05291017160b05040825340b050401141e0b050408172d160b040817160b05330825160b05040114130b05040117160b05040a17160b05321017190504012131160b05040117160b0504302f160b05040117160b05042e17160b2b291025160b2b040117131605040817160504012c141e0504012c172d1604012c171605042c081f160b05040113160504012717160b2b040a2a1b0b050401001413050401171b0504012717160b05291017160b050401 else if page < 2 then 0x160b0504014b else 0
  | 6 => if page < 1 then 0x6a67160b050401160b050401695d1716620b05045d17160b0504685d1716620b05040167160b0504015d17160b0504660117160b0504016517160b0504640117160b0504016317160b050401611716620504016117160b0560040117160b0504015f17160b0504015d17160b05045e5d17165c0b05040117160b0504015b17160b0504015a17160b0504015917160b5805040117160b0504013e17160b0504010a19160b0504013e17160b2405040a00160b0504013e0017160b05040a142a160b050401160b0504014427160b0504015727171916050401271716050401422717160b052904012a160b0504012717160b0504560117160b0504015517160b0504011817160b0504011017160b0504540117160b0504015317160b0504015217160b05040151161e0b0504012717160b05043f1017160b052901100017160b0529101716500b05040117160b0504010817160b0504014f17160b0504014e25160b0504011017161e0b0504080025160b0504010017160b05040817160b0532040117160b0504012c17160b0504012117160b0504014d17160b2b04011017161e0504012c001f160b0504010017160504012c17160b0504012717164c05040127 else if page < 2 then 0x17160b0504016c17160b0504016b else 0
  | 7 => if page < 1 then 0x1716620b0504010017160b0504015d0017160b050401610017160b052904010017160b050401270017160b05040110 else 0
  | 8 => if page < 1 then 0x17160b050401 else 0
  | _ => 0

def counts : ℕ → ℕ
  | 2 => 1
  | 3 => 9
  | 4 => 23
  | 5 => 65
  | 6 => 66
  | 7 => 6
  | 8 => 1
  | _ => 0

def field (table : ℕ → ℕ → ℕ) (k width i : ℕ) :=
  (table k (i/64) >>> (width*(i%64))) % (2^width)

def decode : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, x =>
    let digit := x % 256
    if digit = 0 then [] else BitVec.ofNat 64 (field dictionary 0 64 digit) :: decode n (x >>> 8)

def pool (k i : ℕ) := decode (k+1) (field encodedPool k (8*(k+1)) i)

def entries : ℕ → ℕ
  | 2 => 2
  | 3 => 29
  | 4 => 61
  | 5 => 162
  | 6 => 163
  | 7 => 60
  | _ => 0

def keys (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x6be252cd1e52de55 else 0
  | 3 => if page < 1 then 0xfeb9e527ec3b7469e84649e1e4b46a88e47eaf0ee0c6a984d1e08d26bdc2e62ebc450d06a86e2841935048328e6464488d14ddb588676151876bcddc70aed758703371b66c1d2372683eb29360b72ae95b5f26c552c03f9a3df37b2430297af72ddb88a829dd9b611ea98e5713f7bbc20981c440 else 0
  | 4 => if page < 1 then 0xfe5926fffce7a9d9fc244c76f7a9df8ff3c69f87efe6ba94ec33ff98eae862c3e4d1c193e2ab289be0969f8edf76f1a6d9b0da28ceb8f4f9c79e2901c71dbc79c60e4de3b8842eebb60cbc1aaf7414bead13f8809f49fff09dd222899bc31674965fdc9e962f2b6994d45993944fd03d8f94f53c8cc8c65c87ad36b186ee46cb8414369c77a7d16a7317620671db53396cb7c38f6c1d2372680a472b67515f905ca30f5c5c89807759c077575695ffc551c8cc1d4ed90f2f4a094c5f48bb964e488d2f9946e376272c682bd529dd9b61283158781d69795f100763a50fcc60d10e95e2150bab404a0a650513063dc391000ad850 else 0
  | 5 => if page < 1 then 0x5e6315925df65c50597a182c58d2d48557aaede256b3a05d561124f255797adf54e9433a54ca43c653c7989d51aa14fa4e5f4c964e5dfe334dbf5a434bb9503f488d2f9948626aa7431ce1c442aca6bd423203bc417124a1406609653e3c65ce3b0be0a93780757836edcb1635f0d14f337f3fb2337486b5316df0173163476e30750a6d2f5c3eb62c6868ee2c005d1f28d42376255d3fc522d5206320d5179b204d73f91fdc192d1ece654e1e28aba71c5076721c294b3b1b9ac1c11b862cb81ac345aa1852892b165973c713cac5ee13816dd4133f2da810f470d90f8766b20f624e7d0d99d1960b6461360931d672040e761503383005026ca98c00571ee0 else if page < 2 then 0xc63b305dc6165904c5c8c250c31f05d6c24d6f59bad350a0b897ae1fb5bd4763b43b1c17aff3d44eaf9b512fae62e3bcaaf8f5cea7eccd66a480df77a3b207d5a2c3cad4a10904029eb729559eb67d8a9d0112319cf954219b3eddb796eff8d096e3160b96831b0c94d941ed9069de559008875e8ff9159b8d10bae38c5d54ab8aa14992882e349d87ad36b1879565da81c535fc8162b3797f9ac9e27f0636347ebb04aa7cd952127cbc2ad07c7b26c87c07ff2f788c8eac786158fc779036a97729897176873eea74d70e0772ae1cb2710599eb6ea96c456bbf5fd16a45727169bdf84e690a77fa686f2c336298819161e5024060329ca65f7d93585e983cef else if page < 3 then 0xfef046cbfe454838fd8970f2fa3b4595f8606e60f7f6b20af6302bbcf57e8197f07fd8d1efe6ba94ef281279ee72fecbee011d12ed2ed2f1ec2a12a5e7c5d474e5950f9ee44c99bfe0969f8edd5d4f5fdd28c9cfdd19225cdab06233d5442d3dd3295852d1e48801d0e6fd56cf3b974ece272ca6cdc23a3ecadef410caa5d866c90260c4c74bb8a8 else 0
  | 6 => if page < 1 then 0x62c33785624da85861740a915fbea8665f0220595e983cef5e09442a5cbc840d5b3e74ad56b3a05d56a80ef453c7989d4dc14a9149b0270b4787c71845a17d9142ff50a9423ce218413078af403a28583f04a19d3ecfc3aa3c5a2a8d3abf91613a7488593a55918b3984a1ae36689996356bdad831a7be723163476e30750a6d2db0e07b2c6868ee2c64811d2b9af5122a0358d72539119a24aa6081234186da22f6715522627c8d22239a422193dccb20cdc7001eff4f6d1b616c30199247b415c559a515b8334e14799dba0d7dc7c10d7af6000c2666de0befac440ba184230757eb9606566bf00570d53e05550f40048ad256039d27da0370718702467fb2 else if page < 2 then 0xba8e9bbeb730f5b7b710ae1db411e503b2a6f067b1ba3cecb19a479aadfe33d8ab1e1dadaa41da5fa7d20394a76df0e6a084d7c59fed67029e15b8139de89d109d78d2e19d3b11b69c03c8299b3ce19f9b38fef399772ded996b43f8985d9bec9722ea9696e3160b90f594928aaba5a88aa1499289dafefc8855f89c87f30449877c145e86fdf0788694d2a68603526d8523b59c8477f2a77efc12107ed280aa7cd952127bb52fb87a9d0e1379491c2a792e260278abe4a3782d3bcb7770c98d75a22f93758bdfad748f000973fbff727193de86714aaf6d6f9c017e6f6971dc6e0b18eb6c2e30ce6c24a6306a1edea8699a8cec673de2a1660653c6633fba01 else if page < 3 then 0xff2f8b9cfe72e1bdfe414e9bfd31026afbb659dbf88b6c2cf7f6b20af3e938dbf1def0bff1d90c5bf102e4bbed2ed2f1e62d230ce51c317fe2985052e01cdcb0de5d1c72de136937da7e69ced9d9dd0dd9537342d30dd7ccd26e5703ca106d59c9826d74c81337eac73b156dc6e1d254c63f7ac5c61318b7c354851bc1057cfec074d295bf5090febaf11f01 else 0
  | 7 => if page < 1 then 0xfffa4492fe72e1bdfca901f4f9ed6e8eedf999cbdec203a2ddf29c28dd5a3459dc85062ed9bd0a73d9a32ddcd5be91f6d575a3ced26e5703c9135292c490b053c1cad45ac0a1015cc08b0830bfedd0a9be32bc74bbc05dd4bacb47ceb88c9b73b710ae1db12b935aa5c21fe8a2933cbda0f8ac6e98d5e22d8eb8b44e89dafefc877c145e8619e7d080e3dbec7c77496b7c2645777aaea44975313bfe7289246671eaf08d699a8cec6955227066413b73624fd1fd618c4fd05e9d27d65d93162058e2630d491d5d2c3f7611d13c9f6e6332af48022539119a2523acaa16a79d960c39de9b0c2666de0990f9b50010a60f else 0
  | _ => 0

def targets (k page : ℕ) : ℕ :=
  match k with
  | 2 => if page < 1 then 0x5 else 0
  | 3 => if page < 1 then 0x22d03a1008503b302800331008601040292022003a001a5040204000100008001060000023402000300028601ac03ac032400200180032c01a3 else 0
  | 4 => if page < 1 then 0x8120000050003a30380000305a50a8004240084008600a003a0098001800880063403000002058007a509b7048005ac002200a308060b0600a10b120023088302a0052306800aa40a0301000a0105a307ac062d09a2020009a00a000a06078000800a820421012007a3088107000906028307200a8106200303 else 0
  | 5 => if page < 1 then 0x107020709201a0003210b831fa00b2305a004801920028003a1148609a0190014001080032007a00380028412870623010102210fa00b2016000681080005a30a860a000e2c0c041aa40300198010250121192404861e831d24089305800ba50f2300001580150002a219a2098008031c241ba00a800e800c801b801d2c0484 else if page < 2 then 0x1c831520122f06251c310aa4092c0308112504ac0c8417060cac13a311a00523148002a00d2c060007a20683200613230b800a100c0015861a80088318800d000080092a01a31aa51d800a041822182503030e250406010001240a8500a102010aa00cb21c80062c102317800d800d23088e10811ba21f06170f1e2c0e8103a0 else if page < 3 then 0x1b00162316a3122317000e2320131c2c192101830d25168212810b8103830a0504051b84140607a4068005001d810d821d8305a207001d3104001c810e0019a30e830801 else 0
  | 6 => if page < 1 then 0xf21191a0f242080122101a01fac0781088205831e8113201d0317001b9020301b2420a006231e020b2000000e231620098017a00783068116811637012312861990052c048607200ba51d8303a000210b0620050b0015200aa31e80168017250ba011000d80162220a118ac09850f0019850baa1f000c130a051ca007840a80 else if page < 2 then 0x883180000a4082c1b2511030704142011801d2c02800721082506831a201cb00c850bac1f8317821b850a000b9319b00c86058010801386090000a11224172c188319131783078019251ea10024070205250b0202231f2417801e8219b61ea0062c1c2e0b05172317021e000c0e0b84100010a0182c1d000d211f8b08230380 else if page < 3 then 0x4231a83148620810aa5193505230b80158017a10b2105810da30700203606800880030016830c030b010b9a0fa107030ea217841c3510a21a0006251fa420100c8018030bb5 else 0
  | 7 => if page < 1 then 0x18001830293008800a201860104018d0083023602050285018e01210023028d00a0020e02240282022101200123020100a402200292008702860081022200a1020301060200020c020602370080010000820021028e028000a500000182023100a302230211000600200283021301850192022c01930004 else 0
  | _ => 0

def mix (w : W) : W :=
  let u := w + 0
  let v := (u ^^^ (u >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (v ^^^ (v >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def key (xs : List W) := (xs.foldl (fun h x => h + mix x) (0 : W)).toNat % 4294967296

def search (k h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo+1 < hi then
      let m := (lo+hi)/2
      if field keys k 32 m ≤ h then search k h fuel m hi else search k h fuel lo m
    else lo

def lookup (k : ℕ) (xs : List W) : ℕ × ℕ :=
  let ix := search k (key xs) 14 0 (entries k)
  let slot := field targets k 16 ix
  (slot / 128,slot % 128)

def s01 : Switch := ⟨1,0x2222222222222222,0x4444444444444444⟩
theorem s01_ok : s01.Valid := by unfold Switch.Valid; decide +kernel
def s02 : Switch := ⟨3,0xa0a0a0a0a0a0a0a,0x5050505050505050⟩
theorem s02_ok : s02.Valid := by unfold Switch.Valid; decide +kernel
def s03 : Switch := ⟨7,0xaa00aa00aa00aa,0x5500550055005500⟩
theorem s03_ok : s03.Valid := by unfold Switch.Valid; decide +kernel
def s04 : Switch := ⟨15,0xaaaa0000aaaa,0x5555000055550000⟩
theorem s04_ok : s04.Valid := by unfold Switch.Valid; decide +kernel
def s05 : Switch := ⟨31,0xaaaaaaaa,0x5555555500000000⟩
theorem s05_ok : s05.Valid := by unfold Switch.Valid; decide +kernel
def s12 : Switch := ⟨2,0xc0c0c0c0c0c0c0c,0x3030303030303030⟩
theorem s12_ok : s12.Valid := by unfold Switch.Valid; decide +kernel
def s13 : Switch := ⟨6,0xcc00cc00cc00cc,0x3300330033003300⟩
theorem s13_ok : s13.Valid := by unfold Switch.Valid; decide +kernel
def s14 : Switch := ⟨14,0xcccc0000cccc,0x3333000033330000⟩
theorem s14_ok : s14.Valid := by unfold Switch.Valid; decide +kernel
def s15 : Switch := ⟨30,0xcccccccc,0x3333333300000000⟩
theorem s15_ok : s15.Valid := by unfold Switch.Valid; decide +kernel
def s23 : Switch := ⟨4,0xf000f000f000f0,0xf000f000f000f00⟩
theorem s23_ok : s23.Valid := by unfold Switch.Valid; decide +kernel
def s24 : Switch := ⟨12,0xf0f00000f0f0,0xf0f00000f0f0000⟩
theorem s24_ok : s24.Valid := by unfold Switch.Valid; decide +kernel
def s25 : Switch := ⟨28,0xf0f0f0f0,0xf0f0f0f00000000⟩
theorem s25_ok : s25.Valid := by unfold Switch.Valid; decide +kernel
def s34 : Switch := ⟨8,0xff000000ff00,0xff000000ff0000⟩
theorem s34_ok : s34.Valid := by unfold Switch.Valid; decide +kernel
def s35 : Switch := ⟨24,0xff00ff00,0xff00ff00000000⟩
theorem s35_ok : s35.Valid := by unfold Switch.Valid; decide +kernel
def s45 : Switch := ⟨16,0xffff0000,0xffff00000000⟩
theorem s45_ok : s45.Valid := by unfold Switch.Valid; decide +kernel

def steps : ℕ → List Switch
  | 1 => [s45]
  | 2 => [s34]
  | 3 => [s35]
  | 4 => [s12]
  | 5 => [s01]
  | 6 => [s02]
  | 7 => [s34, s45]
  | 8 => [s35, s45]
  | 9 => [s12, s45]
  | 10 => [s12, s34]
  | 11 => [s12, s35]
  | 12 => [s01, s45]
  | 13 => [s01, s34]
  | 14 => [s01, s35]
  | 15 => [s01, s12]
  | 16 => [s02, s12]
  | 17 => [s02, s45]
  | 18 => [s02, s34]
  | 19 => [s02, s35]
  | 20 => [s12, s34, s45]
  | 21 => [s12, s35, s45]
  | 22 => [s01, s34, s45]
  | 23 => [s01, s35, s45]
  | 24 => [s01, s12, s45]
  | 25 => [s01, s12, s34]
  | 26 => [s01, s12, s35]
  | 27 => [s02, s12, s45]
  | 28 => [s02, s12, s34]
  | 29 => [s02, s12, s35]
  | 30 => [s02, s34, s45]
  | 31 => [s02, s35, s45]
  | 32 => [s03, s14, s25]
  | 33 => [s03, s15, s24]
  | 34 => [s04, s13, s25]
  | 35 => [s04, s15, s23]
  | 36 => [s05, s13, s24]
  | 37 => [s05, s14, s23]
  | 38 => [s01, s12, s34, s45]
  | 39 => [s01, s12, s35, s45]
  | 40 => [s02, s12, s34, s45]
  | 41 => [s02, s12, s35, s45]
  | 42 => [s03, s14, s25, s45]
  | 43 => [s03, s14, s25, s34]
  | 44 => [s03, s14, s25, s35]
  | 45 => [s03, s15, s24, s45]
  | 46 => [s03, s15, s24, s35]
  | 47 => [s03, s15, s24, s34]
  | 48 => [s04, s13, s25, s34]
  | 49 => [s04, s13, s25, s45]
  | 50 => [s04, s13, s25, s35]
  | 51 => [s04, s15, s23, s34]
  | 52 => [s04, s15, s23, s35]
  | 53 => [s04, s15, s23, s45]
  | 54 => [s05, s13, s24, s35]
  | 55 => [s05, s13, s24, s45]
  | 56 => [s05, s13, s24, s34]
  | 57 => [s05, s14, s23, s35]
  | 58 => [s05, s14, s23, s34]
  | 59 => [s05, s14, s23, s45]
  | 60 => [s03, s14, s25, s34, s45]
  | 61 => [s03, s14, s25, s35, s45]
  | 62 => [s03, s15, s24, s35, s45]
  | 63 => [s03, s15, s24, s34, s45]
  | 64 => [s04, s13, s25, s34, s45]
  | 65 => [s04, s13, s25, s35, s45]
  | 66 => [s04, s15, s23, s34, s45]
  | 67 => [s04, s15, s23, s35, s45]
  | 68 => [s05, s13, s24, s35, s45]
  | 69 => [s05, s13, s24, s34, s45]
  | 70 => [s05, s14, s23, s35, s45]
  | 71 => [s05, s14, s23, s34, s45]
  | _ => []

theorem valid (j : ℕ) : ∀ s ∈ steps j, s.Valid := by
  unfold steps
  split <;> simp [s01_ok, s02_ok, s03_ok, s04_ok, s05_ok, s12_ok, s13_ok, s14_ok, s15_ok, s23_ok, s24_ok, s25_ok, s34_ok, s35_ok, s45_ok]

theorem fix (j : ℕ) : reindex (steps j) target = target := by
  unfold steps
  split <;> decide +kernel

def checked (k i : Nat) := decide (pool k i).Nodup && fastClosed target negative pool counts lookup steps k i
theorem root : pool 8 0 = raw := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk2x0 : span (checked 2) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer2 : span (checked 2) 1 0 = true :=
  chunk2x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk3x0 : span (checked 3) 9 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer3 : span (checked 3) 9 0 = true :=
  chunk3x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x0 : span (checked 4) 16 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk4x16 : span (checked 4) 7 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer4 : span (checked 4) 23 0 = true :=
  (@span_join (checked 4) 16 0 7 chunk4x0 chunk4x16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x0 : span (checked 5) 16 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x16 : span (checked 5) 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x32 : span (checked 5) 16 32 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x48 : span (checked 5) 16 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk5x64 : span (checked 5) 1 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer5 : span (checked 5) 65 0 = true :=
  (@span_join (checked 5) 64 0 1 (@span_join (checked 5) 48 0 16 (@span_join (checked 5) 32 0 16 (@span_join (checked 5) 16 0 16 chunk5x0 chunk5x16) chunk5x32) chunk5x48) chunk5x64)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x0 : span (checked 6) 16 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x16 : span (checked 6) 16 16 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x32 : span (checked 6) 16 32 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x48 : span (checked 6) 16 48 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk6x64 : span (checked 6) 2 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer6 : span (checked 6) 66 0 = true :=
  (@span_join (checked 6) 64 0 2 (@span_join (checked 6) 48 0 16 (@span_join (checked 6) 32 0 16 (@span_join (checked 6) 16 0 16 chunk6x0 chunk6x16) chunk6x32) chunk6x48) chunk6x64)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk7x0 : span (checked 7) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer7 : span (checked 7) 6 0 = true :=
  chunk7x0

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem chunk8x0 : span (checked 8) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer8 : span (checked 8) 1 0 = true :=
  chunk8x0

theorem verified : ∀ k ≤ 8, ∀ i < counts k, checked k i = true := by
  intro k hk
  interval_cases k
  · simp [counts]
  · simp [counts]
  · intro i hi; exact span_member layer2 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer3 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer4 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer5 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer6 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer7 i (Nat.zero_le i) (by simpa [counts] using hi)
  · intro i hi; exact span_member layer8 i (Nat.zero_le i) (by simpa [counts] using hi)
theorem lower {k : Nat} {s : Finset W} (run : Cone target k s) (sub : s ⊆ insert 0 raw.toFinset) : 9 ≤ k := by
  by_contra! short
  have eq := run.initial nonzero raw essential sub
  rw [eq,←root] at run
  apply closed_excludes target nonzero negative neg pool counts lookup steps valid fix 8
    (fun k hk i hi => of_decide_eq_true (Bool.and_eq_true_iff.mp (verified k hk i hi)).1)
    (fun k hk i hi => fastClosed_sound target nonzero negative pool counts lookup steps k i (Bool.and_eq_true_iff.mp (verified k hk i hi)).2)
    8 le_rfl 0 (by decide +kernel) k (by omega) run

end SignedFrontier.SmallCert.Tri

namespace TableLink
open SignedFrontier

def initial : List W := [0, ~~~(0 : W)] ++ SmallCert.Tri.raw ++ SmallCert.Tri.raw.map (fun w => ~~~w)

def assignment (r : Fin 64) (v : Fin 6) : Bool := r.val.testBit v.val

theorem rawTable : ∀ r : Fin 64, initial.map (fun u => u.getLsbD r.val) =
    Graph8.signedStart6 (assignment r) := by decide +kernel

theorem goalTable : ∀ r : Fin 64, SmallCert.Tri.target.getLsbD r.val =
    Graph8.target6 (assignment r) := by decide +kernel

theorem readDefault (xs : List W) (j r : ℕ) :
    (xs.getD j 0).getLsbD r = (xs.map (fun u => u.getLsbD r)).getD j false := by
  by_cases hj : j < xs.length
  · rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem addRow (xs : List W) (ij : ℕ × ℕ) (r : ℕ) (hr : r < 64) :
    (add xs ij).map (fun u => u.getLsbD r) =
      PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r)) ij := by
  simp only [add,PetersenSignedSlice.addPair,List.map_append,List.map_cons,List.map_nil,
      BitVec.getLsbD_and,BitVec.getLsbD_not,hr,decide_true,Bool.true_and,readDefault]

theorem foldRow (p : List (ℕ × ℕ)) (xs : List W) (r : Fin 64) :
    (p.foldl add xs).map (fun u => u.getLsbD r.val) =
      p.foldl PetersenSignedSlice.addPair (xs.map (fun u => u.getLsbD r.val)) := by
  induction p generalizing xs with
  | nil => rfl
  | cons ij tail ih =>
    simp only [List.foldl_cons,ih,addRow _ _ _ r.isLt]

theorem wordOfSolution (p : List (ℕ × ℕ)) (o : ℕ)
    (hit : ∀ y, Graph8.signed6 p o y = Graph8.target6 y) :
    canonical (evaluate p initial o) = SmallCert.Tri.target := by
  have eq : evaluate p initial o = SmallCert.Tri.target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i,hi⟩
    change ((p.foldl add initial).getD o 0).getLsbD r.val = _
    rw [readDefault,foldRow p initial r,rawTable r]
    exact (hit (assignment r)).trans (goalTable r).symm
  rw [eq]
  decide +kernel

theorem lowerSix (p : List (ℕ × ℕ)) (o : ℕ) (hit : canonical (evaluate p initial o) = SmallCert.Tri.target) :
    9 ≤ p.length := by
  have inside : {SmallCert.Tri.target} ⊆ available (p.foldl add initial) := by
    apply Finset.singleton_subset_iff.mpr
    rw [←hit]
    exact available_read _ _
  obtain ⟨k,s,le,access,run⟩ := extract p initial SmallCert.Tri.target 0 {SmallCert.Tri.target} Cone.done inside
  have start : available initial = insert 0 SmallCert.Tri.raw.toFinset := by decide +kernel
  rw [start] at access
  have low := SmallCert.Tri.lower run access
  omega

theorem six (p : List (ℕ × ℕ)) (o : ℕ) (hit : ∀ y, Graph8.signed6 p o y = Graph8.target6 y) :
    9 ≤ p.length :=
  lowerSix p o (wordOfSolution p o hit)

end TableLink

namespace Graph8
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem replacement (C : Circuit) (ok : FanInTwo C) (hit : ∀ x, circuitFun 8 C x = target8 x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 8 D x = posted x := by
  by_cases mono : Monotone2 C
  · exact ⟨C, mono, le_rfl, fun x => (hit x).trans (table x).symm⟩
  · obtain ⟨p1,o1,sz1,ev1⟩ := pin8 C ok hit
    obtain ⟨p2,o2,sz2,ev2⟩ := pin7 p1 o1 ev1
    have low := TableLink.six p2 o2 ev2
    have paid (gs : List Gate) : (gs.map PetersenSignedSlice.Paid).sum ≤ gs.length ∧
        ((gs.map PetersenSignedSlice.Paid).sum = gs.length →
          ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) →
            (g.op = .and ∨ g.op = .or)) := by
      induction gs with
      | nil => simp
      | cons g t ih =>
        have cap : PetersenSignedSlice.Paid g ≤ 1 := by unfold PetersenSignedSlice.Paid; split <;> (first | decide | split <;> decide)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro eq u mem kind
        rcases List.mem_cons.mp mem with rfl | tail
        · rcases kind with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · have := ih.1
            simp [PetersenSignedSlice.Paid, h, GateOp.eval] at eq
            omega
        · exact ih.2 (by omega) _ tail kind
    obtain ⟨cap, full⟩ := paid C.gates
    have strict : (C.gates.map PetersenSignedSlice.Paid).sum < C.gates.length := by
      by_contra! fail
      apply mono
      intro g hg
      exact ⟨full (by omega) _ hg (ok g hg).1, (ok g hg).2⟩
    exact ⟨witness, legal, by rw [size]; change 12 ≤ C.gates.length; omega, value⟩

end Graph8

end PEqualNP.Outside.L_meta_14088

open PEqualNP.Outside.L_meta_14088

theorem PEqualNP.Outside.L_meta_14088 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 1, 6, 4, 6, 0, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,o⟩
  have ok : PEqualNP.MetaComplexity.FanInTwo C := legal
  have hit : ∀ x, PEqualNP.MetaComplexity.circuitFun 8 C x = Graph8.target8 x :=
    fun x => (computes x).trans (Graph8.table x)
  obtain ⟨D,mono,bound,evaluates⟩ := Graph8.replacement C ok hit
  exact ⟨D.gates,D.output,mono,bound,evaluates⟩
