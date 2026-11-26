import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18938.Helpers


open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, ite_eq_right hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, ite_eq_left rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n m : ℕ} (ρ : (Fin m → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext m new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi


namespace Mono


def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma append_mono (x y : List Bool) (a b : Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (x ++ [a]).getD i false = true → (y ++ [b]).getD i false = true := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hl]
    cases he : i - y.length <;> simp_all

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (h : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro hx i hi
    exact h i (hx i hi)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i hx⟩

lemma run_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, (run gs (x ++ [_])).getD i false = true →
      (run gs (y ++ [_])).getD i false = true
    apply ih (fun q hq => hm q (List.mem_cons_of_mem g hq)) _ _ (by simp [hl])
    exact append_mono x y _ _ hl h (gate_mono g (hm g (by simp)) _ _ h)


end Mono

lemma W_prefix {n : ℕ} (pre post : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n+pre.length) :
    (W (pre++post) x).getD i false = (W pre x).getD i false := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    rw [← List.append_assoc,W_val,ite_eq_right (by simp only [List.length_append];omega),ih]

lemma dead_prefix {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m))
    (hC : PEqualNP.TopForm.IsAO2 n C) (pre post : List Gate)
    (hs : pre++post=C.gates) (i : ℕ) (hi : i<n+pre.length)
    (hd : (C.wires (List.ofFn (fun k => (p k).isSome))).getD i false = false) :
    ∀ x : Fin m → Bool,(W pre (fun k => (p k).elim false x)).getD i false = false := by
  intro x
  have hpre : ∀ g ∈ pre,g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    apply hC.1 g
    rw [← hs]
    exact List.mem_append_left _ hg
  have input : ∀ j,(List.ofFn (fun k => (p k).elim false x)).getD j false = true →
      (List.ofFn (fun k => (p k).isSome)).getD j false = true := by
    intro j hj
    by_cases h : j<n
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left h,Option.getD_some] at hj ⊢
      cases hp : p ⟨j,h⟩ <;> simp_all
    · simp [List.getD_eq_getElem?_getD,h] at hj
  have hm := Mono.run_mono pre hpre _ _ (by simp) input i
  have ht : (W pre (fun k => (p k).isSome)).getD i false = false := by
    rw [← W_prefix pre post _ i hi,hs]
    exact hd
  cases hx : (W pre (fun k => (p k).elim false x)).getD i false with
  | false => rfl
  | true =>
    have h := hm hx
    change (W pre (fun k => (p k).isSome)).getD i false = true at h
    rw [ht] at h
    cases h

lemma gate_dead_rep {n m : ℕ} (ρ : (Fin m → Bool) → Fin n → Bool)
    (old new : List Gate) (op : GateOp) (a b : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hr : ∀ i,Rep new (fun x => (W old (ρ x)).getD i false))
    (hd : (∀ x,(W old (ρ x)).getD a false = false) ∨
      (∀ x,(W old (ρ x)).getD b false = false)) :
    Rep new (fun x => op.eval [((W old (ρ x)).getD a false),((W old (ρ x)).getD b false)]) := by
  rcases hop with rfl | rfl
  · apply Or.inl
    refine ⟨false,?_⟩
    intro x
    dsimp only
    rcases hd with hd | hd <;> rw [hd x] <;> simp [GateOp.eval]
  · rcases hd with hd | hd
    · exact rep_congr (fun x => by rw [hd x]; simp [GateOp.eval]) (hr b)
    · exact rep_congr (fun x => by rw [hd x]; simp [GateOp.eval]) (hr a)




def top {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (t : ℕ) : Bool :=
  (C.wires (List.ofFn (fun k => (p k).isSome))).getD t false

def cost {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool) (j : ℕ) : Bool :=
  U (n+j) && (C.gates.getD j ⟨.or,[]⟩).inputs.all (top C p)

def Inv {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate,(∀ g ∈ new,Fan g) ∧ RB m new ∧
    new.length ≤ ((List.range old.length).filter (cost C p U)).length ∧
    ∀ t,U t=true → Rep new (fun x => (W old (fun k => (p k).elim false x)).getD t false)

lemma inv_initial {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool) : Inv C p U [] := by
  refine ⟨[],by simp,?_,by simp,?_⟩
  · intro j hj; simp at hj
  · intro t _
    by_cases ht : t<n
    · have oldval : ∀ x : Fin m → Bool,
          (W [] (fun k => (p k).elim false x)).getD t false = (p ⟨t,ht⟩).elim false x := by
        intro x
        simp [W,List.getD_eq_getElem?_getD,ht]
      cases hp : p ⟨t,ht⟩ with
      | none => exact Or.inl ⟨false,fun x => by dsimp only;rw [oldval,hp];rfl⟩
      | some v =>
        refine Or.inr ⟨v.val,by simpa using v.isLt,?_⟩
        intro x
        dsimp only
        rw [oldval,hp]
        simp [W,List.getD_eq_getElem?_getD,v.isLt]
    · exact Or.inl ⟨false,fun x => List.getD_eq_default _ _ (by rw [W_len];simp;omega)⟩

lemma inv_step {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (closed : ∀ j < C.size,U (n+j)=true → top C p (n+j)=true →
      ∀ i ∈ (C.gates.getD j ⟨.or,[]⟩).inputs,top C p i=true → U i=true)
    (pre post : List Gate) (g : Gate) (hs : pre++g::post=C.gates) (h : Inv C p U pre) : Inv C p U (pre++[g]) := by
  obtain ⟨new,hfan,hrb,hl,hr⟩ := h
  have hmem : g ∈ C.gates := by rw [← hs];simp
  have hlen := hC.2.2 g hmem
  obtain ⟨a,b,hab⟩ : ∃ a b,g.inputs=[a,b] := by
    rcases hh : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,tl⟩⟩⟩ <;> simp_all
  have hg : C.gates.getD pre.length ⟨GateOp.or,[]⟩ = g := by
    rw [← hs]
    simp [List.getD_eq_getElem?_getD]
  have hj : pre.length<C.size := by change pre.length<C.gates.length;rw [← hs];simp
  have hb (i : ℕ) (hi : i ∈ g.inputs) : i<n+pre.length := by
    apply hC.2.1 pre.length hj i
    change i ∈ (C.gates.getD pre.length ⟨GateOp.or,[]⟩).inputs
    rw [hg]
    exact hi
  have build : ∃ new',Ext m new new' ∧
      (cost C p U pre.length=false → new'=new) ∧
      (U (n+pre.length)=true → Rep new' (fun x => g.op.eval (g.inputs.map fun i => (W pre (fun k => (p k).elim false x)).getD i false))) := by
    cases hu : U (n+pre.length) with
    | false => exact ⟨new,Or.inl rfl,fun _ => rfl,by simp [hu]⟩
    | true =>
      cases ht : top C p (n+pre.length) with
      | false =>
        refine ⟨new,Or.inl rfl,fun _ => rfl,fun _ => Or.inl ⟨false,?_⟩⟩
        intro x
        have hd := dead_prefix C p hC (pre++[g]) post (by simpa [List.append_assoc] using hs)
          (n+pre.length) (by simp) ht x
        simpa only [W_val,↓reduceIte] using hd
      | true =>
        have hrep (i : ℕ) (hi : i ∈ g.inputs) : Rep new (fun x => (W pre (fun k => (p k).elim false x)).getD i false) := by
          cases hv : top C p i with
          | false => exact Or.inl ⟨false,dead_prefix C p hC pre (g::post) hs i (hb i hi) hv⟩
          | true => exact hr i (closed pre.length hj hu ht i (by rwa [hg]) hv)
        cases hc : g.inputs.all (top C p) with
        | false =>
          have hd : (∀ x : Fin m → Bool,(W pre (fun k => (p k).elim false x)).getD a false=false) ∨
              (∀ x : Fin m → Bool,(W pre (fun k => (p k).elim false x)).getD b false=false) := by
            have hc' : top C p a=false ∨ top C p b=false := by
              simpa only [hab,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_false_iff] using hc
            rcases hc' with ha | hb'
            · exact Or.inl (dead_prefix C p hC pre (g::post) hs a (hb a (by simp [hab])) ha)
            · exact Or.inr (dead_prefix C p hC pre (g::post) hs b (hb b (by simp [hab])) hb')
          refine ⟨new,Or.inl rfl,fun _ => rfl,fun _ => ?_⟩
          rw [hab]
          simp only [List.map_cons,List.map_nil]
          rcases hC.1 g hmem with hop | hop
          · refine Or.inl ⟨false,?_⟩
            intro x
            dsimp only
            rcases hd with hd | hd <;> rw [hd x] <;> simp [hop,GateOp.eval]
          · rcases hd with hd | hd
            · exact rep_congr (fun x => by rw [hd x];simp [hop,GateOp.eval]) (hrep b (by simp [hab]))
            · exact rep_congr (fun x => by rw [hd x];simp [hop,GateOp.eval]) (hrep a (by simp [hab]))
        | true =>
          have hcost : cost C p U pre.length=true := by unfold cost;rw [hu,hg,hc];rfl
          rcases hC.1 g hmem with hop | hop
          · obtain ⟨new',he,hrep'⟩ := rep_and new _ _ (hrep a (by simp [hab])) (hrep b (by simp [hab]))
            refine ⟨new',he,by simp [hcost],fun _ => ?_⟩
            exact rep_congr (fun x => by simp [hab,hop,GateOp.eval]) hrep'
          · obtain ⟨new',he,hrep'⟩ := rep_or new _ _ (hrep a (by simp [hab])) (hrep b (by simp [hab]))
            refine ⟨new',he,by simp [hcost],fun _ => ?_⟩
            exact rep_congr (fun x => by simp [hab,hop,GateOp.eval]) hrep'
  obtain ⟨new',he,hcheap,hrep⟩ := build
  refine ⟨new',?_,?_,?_,?_⟩
  · rcases he with rfl | ⟨g',rfl,hg',_⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · simpa using (show Fan q from (List.mem_singleton.mp hq) ▸ hg')
  · rcases he with rfl | ⟨g',rfl,_,hb'⟩
    · exact hrb
    · exact rb_snoc hrb hb'
  · simp only [List.length_append,List.length_singleton,List.range_succ,List.filter_append]
    cases hc : cost C p U pre.length with
    | false => rw [hcheap hc];simpa [hc] using hl
    | true =>
      have hlen' : new'.length ≤ new.length+1 := by
        rcases he with rfl | ⟨g',rfl,_⟩ <;> simp
      simpa [hc] using (show new'.length ≤ ((List.range pre.length).filter (cost C p U)).length+1 from by omega)
  · intro t hu
    by_cases ht : t=n+pre.length
    · exact rep_congr (fun x => by rw [W_val,ite_eq_left ht]) (hrep (ht ▸ hu))
    · exact rep_congr (fun x => by rw [W_val,ite_eq_right ht]) (rep_mono he _ (hr t hu))

lemma inv_all {n m : ℕ} (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (closed : ∀ j < C.size,U (n+j)=true → top C p (n+j)=true →
      ∀ i ∈ (C.gates.getD j ⟨.or,[]⟩).inputs,top C p i=true → U i=true) : Inv C p U C.gates := by
  have aux : ∀ post pre,pre++post=C.gates → Inv C p U pre → Inv C p U C.gates := by
    intro post
    induction post with
    | nil =>
      intro pre hs hi
      rw [List.append_nil] at hs
      exact hs ▸ hi
    | cons g post ih =>
      intro pre hs hi
      exact ih (pre++[g]) (by simpa [List.append_assoc] using hs) (inv_step C p U hC closed pre post g hs hi)
  exact aux C.gates [] rfl (inv_initial C p U)

lemma zero_wires {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs,Fan g) :
    ∀ t,(W gs (fun _ : Fin n => false)).getD t false = false := by
  induction gs using List.reverseRecOn with
  | nil => intro t; simp [W,List.getD_eq_getElem?_getD]
  | append_singleton gs g ih =>
    have hpre := ih (fun q hq => hg q (List.mem_append_left _ hq))
    have hgf := hg g (List.mem_append_right _ (List.mem_singleton_self g))
    obtain ⟨a,b,hab⟩ : ∃ a b,g.inputs=[a,b] := by
      have hl := hgf.2
      rcases hh : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,tl⟩⟩⟩ <;> simp_all
    intro t
    rw [W_val]
    split_ifs
    · rw [hab]
      simp only [List.map_cons,List.map_nil,hpre]
      rcases hgf.1 with he | he <;> rw [he] <;> rfl
    · exact hpre t

theorem compact (n m : ℕ) (C : Circuit) (p : Fin n → Option (Fin m)) (U : ℕ → Bool)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hout : U C.output=true)
    (closed : ∀ j < C.size,U (n+j)=true → top C p (n+j)=true →
      ∀ i ∈ (C.gates.getD j ⟨.or,[]⟩).inputs,top C p i=true → U i=true) :
    ∃ D : Circuit,PEqualNP.TopForm.IsAO2 m D ∧
      D.size ≤ ((List.range C.size).filter (cost C p U)).length ∧
      ∀ x : Fin m → Bool,D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => (p i).elim false x)) := by
  obtain ⟨new,hfan,hrb,hl,hr⟩ := inv_all C p U hC closed
  rcases hr C.output hout with ⟨c,hc⟩ | ⟨j,hj,hv⟩
  · have hz : (fun i => (p i).elim false (fun _ : Fin m => false)) = (fun _ : Fin n => false) := by
      funext i;cases p i <;> rfl
    have hzero := hc (fun _ => false)
    dsimp only at hzero
    rw [hz,zero_wires C.gates (fun g hg => ⟨hC.1 g hg,hC.2.2 g hg⟩)] at hzero
    subst c
    refine ⟨⟨[],m⟩,?_,by simp [Circuit.size],?_⟩
    · constructor
      · intro g hg;simp at hg
      · constructor
        · intro j hj;simp at hj
        · intro g hg;simp at hg
    · intro x
      change (List.ofFn x).getD m false = (W C.gates (fun i => (p i).elim false x)).getD C.output false
      dsimp only at hc
      rw [hc x]
      exact List.getD_eq_default _ _ (by simp)
  · refine ⟨⟨new,j⟩,?_,hl,hv⟩
    constructor
    · exact fun g hg => (hfan g hg).1
    · exact ⟨hrb,fun g hg => (hfan g hg).2⟩


lemma trim (n : ℕ) (C : Circuit) (s : Fin n) (U : ℕ → Bool) (hC : PEqualNP.TopForm.IsAO2 n C) :
    let T := PEqualNP.ReadTwo.wval C (fun i : Fin n => decide (i ≠ s))
    U C.output=true →
    (∀ j < C.size,U (n+j)=true → T (n+j)=true →
      ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,T i=true → U i=true) →
    ∃ D : Circuit,PEqualNP.TopForm.IsAO2 n D ∧
      D.size ≤ ((List.range C.size).filter (fun j => U (n+j) && (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.all T)).length ∧
      ∀ x : Fin n → Bool,D.eval (List.ofFn x)=C.eval (List.ofFn fun i => if i=s then false else x i) := by
  dsimp only
  intro ho hclose
  let p : Fin n → Option (Fin n) := fun i => if i=s then none else some i
  have he : (fun i => (p i).isSome) = (fun i : Fin n => decide (i≠s)) := by
    funext i
    by_cases h : i=s <;> simp [p,h]
  have ht : top C p = PEqualNP.ReadTwo.wval C (fun i : Fin n => decide (i≠s)) := by
    unfold top PEqualNP.ReadTwo.wval
    rw [he]
  have closed : ∀ j < C.size,U (n+j)=true → top C p (n+j)=true →
      ∀ i ∈ (C.gates.getD j ⟨.or,[]⟩).inputs,top C p i=true → U i=true := by
    simpa only [ht,PEqualNP.MetaComplexity.NestedCover.gateAt] using hclose
  obtain ⟨D,ha,hs,hv⟩ := compact n n C p U hC ho closed
  refine ⟨D,ha,?_,?_⟩
  · change D.size ≤ ((List.range C.size).filter (fun j => U (n+j) && (C.gates.getD j ⟨.or,[]⟩).inputs.all (top C p))).length at hs
    rw [ht] at hs
    exact hs
  · intro x
    rw [hv x]
    congr 2
    funext i
    by_cases h : i=s <;> simp [p,h]
end PEqualNP.Outside.L_meta_18938.Helpers


theorem PEqualNP.Outside.L_meta_18938 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : ℕ → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     have x6 : ℕ → Bool := PEqualNP.ReadTwo.wval x2 fun (x6 : Fin x1) => Decidable.decide (x6 ≠ x3);     x4 x2.output = Bool.true → (∀ x8 < x2.size, x4 (x1 + x8) = Bool.true → x6 (x1 + x8) = Bool.true → ∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, x6 x12 = Bool.true → x4 x12 = Bool.true) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x9 ∧ x9.size ≤ (List.filter (fun (x10 : ℕ) => x4 (x1 + x10) && (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs.all x6) (List.range x2.size)).length ∧ ∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x2.eval (List.ofFn fun (x11 : Fin x1) => if x11 = x3 then Bool.false else x10 x11)) := by
  exact PEqualNP.Outside.L_meta_18938.Helpers.trim
