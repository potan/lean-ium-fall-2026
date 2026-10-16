/-!
# Seminar 2
Propositions as types
-/

/- Implicit arguments -/

def id1 : (α : Type) → α → α := λ _ x ↦ x

#check id1
#check id1 Nat 5
#check id1 Prop True
#check_failure id1 5

def id2 : {α : Type} → α → α := λ x ↦ x

#check id2
#check id2 5
#check id2 True
#check_failure id2 Nat 5
#check @id2
#check @id2 Nat 5

def compose {α β γ : Type} (f : α → β) (g : β → γ) :
  α → γ := λ x ↦ g (f x)

/- Structures -/

structure PointNatNat : Type where
  mk ::
  x : Nat
  y : Nat

#check PointNatNat
#check PointNatNat.mk
#check PointNatNat.x
#check PointNatNat.y


#check PointNatNat.mk 1 2
#check ({ x := 1, y := 2 } : PointNatNat)
#check ({ y := 2, x := 1 } : PointNatNat)
#check_failure {x := 1, y := 2}

#check_failure {x := 1, y := 2 : Nat}
#check {x := 1, y := 2 : PointNatNat}
#check {x := 1, y := (2 : Nat) : PointNatNat}

def pp : PointNatNat := {x := 0, y := 0}

#eval {pp with x := 3}

#check (⟨0, 1⟩ : PointNatNat)
#eval pp.1
#eval pp.2

structure PointNatNatNat extends PointNatNat where
  z : Nat

#check {x := 0, y := 0, z := 0 : PointNatNatNat}
#check PointNatNatNat.toPointNatNat

structure Prod' (A B : Type) : Type where
  fst : A
  snd : B

#check Prod' Nat Prop

#check Prod
#print Prod
#check Prod Nat Nat
#check Nat × Nat

structure PointType where
  A : Type
  x : A
  y : A

#check { A := Nat, x := 0, y := 0 : PointType }

/- Propositions as Types -/
#check Prop
#check False
#check True

section CH
  axiom And' : Prop → Prop → Prop
  axiom Implies : Prop → Prop → Prop

  variable (p q r : Prop)

  #check Implies (And' p q) (And' q p)

  variable (Proof : Prop → Type)

  variable (modus_ponens : Proof (Implies p q) → Proof p → Proof q)
  variable (implies_intro : (Proof p → Proof q) → Proof (Implies p q))

  /-
  First, we can get rid of `Proof` and identify `Proof p` with `p` itself!
  Second, above axioms show that:
    modus_ponens p q  : Implies p q → (p → q)
    implies_intro p q : (p → q) → Implies p q

  So, we can try identifying Implies p q with the λction space (p → q)
  -/

  #check p

  variable (t : p)
  #check t

  #check (p → q → p)
end CH

/- Implication -/
variable {p q r : Prop}

theorem t1 : p → q → p := λ hp _ ↦ hp

#check t1
#print t1

theorem t1' : p → q → p :=
  λ hp : p ↦
  λ _ : q ↦
  show p from hp

theorem t2 (hp : p) : q → p := t1 hp

example : p → p := id
example : (p → q) → (q → r) → p → r := by
  intro f g p
  apply g
  apply f
  exact p
example : (p → (q → r)) → (p → q) → p → r := by
  intro f g p
  apply f
  exact p
  apply g
  exact p

/- And -/
#check And
#print And
#check And p q
#check p ∧ q

example : p → q → p ∧ q := λ hp hq ↦ ⟨hp, hq⟩
example : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.right, h.left⟩

/- Or -/

#check Or
#print Or
#check Or p q
#check p ∨ q
#check Or.inl
#check Or.inr
#check Or.elim

example : p ∨ q → q ∨ p :=
  λ h ↦ Or.elim h (λ hp ↦ Or.inr hp) (λ hq ↦ Or.inl hq)

/- True -/

#check True
#check True.intro
#check trivial
#print trivial

example : p → True :=
  λ _ ↦ trivial
example : (p ∨ True) ∧ True := sorry

/- False -/

#check False
#check False.elim

example : False → p := False.elim

/- Not -/
#check Not
#print Not
#check Not p
#check ¬ p

example : (p → ¬ p → q) :=
  λ hp hnp ↦ False.elim (hnp hp)

example : (p → q) → (¬ q → ¬ p) := by
  intro h nq tp
  apply nq
  apply h
  exact tp

/- Iff -/

#check Iff
#print Iff
#check Iff p q
#check p ↔ q

example : p ↔ p ∧ p :=
  ⟨λ hp ↦ ⟨hp, hp⟩,
  λ hpp ↦ hpp.left⟩
example : p ∧ q ↔ q ∧ p := by
  constructor
  · intro ⟨ph, qh⟩
    exact ⟨qh, ph⟩
  · intro ⟨qh, ph⟩
    exact ⟨ph, qh⟩

/- Local definitions -/
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) ↦
      have hp : p := h.left
      Or.elim (h.right)
        (λ hq : q ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (λ hr : r ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (λ h : (p ∧ q) ∨ (p ∧ r) ↦
      Or.elim h
        (λ hpq : p ∧ q ↦
          have hp : p := hpq.left
          let hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (λ hpr : p ∧ r ↦
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

/- Classical logic -/

#check Classical.em
#check absurd

example : ¬¬ p → p :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ hp)
    (λ hnp ↦ False.elim (h hnp))
example : ¬(p ∧ ¬q) → (p → q) := fun h hp =>
  Or.elim (Classical.em q)
    id
    fun nq => False.elim (h ⟨hp, nq⟩)
/-!
# Exercises
-/

section hw
  /- Classical.em is not required: -/
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    ⟨fun rb =>
      ⟨rb.left.left,⟨rb.left.right,rb.right⟩⟩,
     fun rb =>
      ⟨⟨rb.left,rb.right.left⟩,rb.right.right⟩⟩
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨
     fun a =>
       Or.elim a
         (fun hpq => Or.elim hpq Or.inl (Or.inr ∘ Or.inl))
         (Or.inr ∘ Or.inr),
     fun a =>
       Or.elim a
         (Or.inl ∘ Or.inl)
         fun aa => Or.elim aa
                     (Or.inl ∘ Or.inr)
                     Or.inr⟩
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := ⟨
      (fun h => Or.elim h (fun ph => ⟨Or.inl ph, Or.inl ph⟩) (fun ⟨qh, rh⟩ => ⟨Or.inr qh, Or.inr rh⟩)),
      (fun ⟨qh, rh⟩ => Or.elim qh Or.inl (fun qh => Or.elim rh Or.inl fun rh => Or.inr ⟨qh, rh⟩))⟩
  example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨
      (fun f h => f h.left h.right),
      (fun f ph qh => f ⟨ph, qh⟩)⟩
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := ⟨
      (fun f => ⟨f ∘ Or.inl, f ∘ Or.inr⟩),
      (fun ⟨ph, qh⟩ h => Or.elim h ph qh)⟩
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨
    (fun h => ⟨h ∘ Or.inl, h ∘ Or.inr⟩),
    (fun ng ps => Or.elim ps ng.left ng.right)
  ⟩
  example : ¬p ∨ ¬q → ¬(p ∧ q) := fun ng ⟨ph, qh⟩ => Or.elim ng (fun f => f ph) (fun f => f qh)
  example : ¬(p ∧ ¬p) := fun ⟨ps, ng⟩ => ng ps
  example : p ∧ ¬q → ¬(p → q) := fun ⟨ph, nqh⟩ h => nqh (h ph)
  example : ¬p → (p → q) := Function.comp False.elim
  example : (¬p ∨ q) → (p → q) := fun h ph => Or.elim h (fun np => False.elim (np ph)) id
  example : p ∨ False ↔ p := ⟨(fun h => Or.elim h id False.elim), Or.inl⟩
  example : p ∧ False ↔ False := ⟨And.right, False.elim⟩
  example : (p → q) → (¬q → ¬p) := fun h hnq hp => hnq (h hp)

  /- Classical.em is required: -/
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun h =>
    Or.elim (Classical.em q)
      (fun qh => Or.inl (fun _ => qh))
      (fun qh => Or.inr (fun ph => Or.elim (h ph) (False.elim ∘ qh) id))
  example : ¬(p ∧ q) → ¬p ∨ ¬q := fun h =>
    Or.elim (Classical.em p)
      (fun hp => Or.inr (fun hq => h ⟨hp, hq⟩))
      Or.inl
  example : ¬(p → q) → p ∧ ¬q := fun h =>
    Or.elim (Classical.em p)
      (fun hp => Or.elim (Classical.em q) (fun hq => False.elim (h (fun _ => hq))) (fun hq => ⟨hp, hq⟩))
      (fun hnp => False.elim (h (fun hp => False.elim (hnp hp))))
  example : (p → q) → (¬p ∨ q) := fun h =>
    Or.elim (Classical.em p)
      (Or.inr ∘ h)
      Or.inl
  example : (¬q → ¬p) → (p → q) := fun h =>
    Or.elim (Classical.em q)
      (λ hq _ => hq)
      (λ hnq hp => False.elim (h hnq hp))
  example : p ∨ ¬p := Classical.em p
  example : (((p → q) → p) → p) := fun h =>
    Or.elim (Classical.em p)
      id
      (λ hnp => h (False.elim ∘ hnp))
end hw
