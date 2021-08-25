
notation:65 "ℕ" => Nat 
open Nat
def fact : ℕ → ℕ 
| zero => 1
| succ n' => fact n' * succ n'

inductive fact_state :=
| AnswerIs (answer : ℕ)
| WithAccumulator (input accumulator : ℕ)

inductive fact_init (original_input : ℕ) : fact_state → Prop :=
| FactInit : fact_init original_input (fact_state.WithAccumulator original_input 1)
inductive fact_final : fact_state → Prop :=
| FactFinal : ∀ ans, fact_final (fact_state.AnswerIs ans)
inductive fact_step : fact_state → fact_state → Prop :=
| FactDone : ∀ acc,
  fact_step (fact_state.WithAccumulator zero acc) (fact_state.AnswerIs acc)
| FactStep : ∀ n acc,
  fact_step (fact_state.WithAccumulator (succ n) acc) (fact_state.WithAccumulator n (acc * succ n))


-- -------------- Transition Relation ---------------------
inductive trc {A} (R : A → A → Prop) : A → A → Prop :=
| TrcRefl : ∀ x, trc R x x
| TrcFront : ∀ x y z, R x y → trc R y z → trc R x z


theorem trc_transitive : ∀ {A} (R : A → A → Prop) x y,
  trc R x y → ∀ z, trc R y z → trc R x z := by
  intros A R x y TR
  induction TR with
  | TrcRefl a => 
    intros z TR
    assumption
  | TrcFront _ _ _ _ _ ih =>
    intros
    apply trc.TrcFront
    assumption
    apply ih
    assumption

  postfix:max "^*" => trc

-- -------------- Transition Relation ---------------------

theorem succ12 : ∀ n, succ n = n + 1 := by
  intro 
  simp 
 theorem x : (succ 2 * succ 1) = 6 := by
    simp 

open trc 
open fact_step
example : fact_step^* (fact_state.WithAccumulator 3 1) (fact_state.AnswerIs 6) :=
  by 
    apply TrcFront
    apply FactStep
    simp 
    apply TrcFront
    apply FactStep
    simp [x]
    apply TrcFront
    apply FactStep
    simp
    apply TrcFront
    apply FactDone
    apply TrcRefl

    
example : fact_step^* (fact_state.WithAccumulator 3 1) (fact_state.AnswerIs 6) :=
  by 
    repeat 
      apply TrcFront
      apply FactStep
      simp [x]
    apply TrcFront
    apply FactDone
    apply TrcRefl
    done
    
example : fact_step^* (fact_state.WithAccumulator 3 1) (fact_state.AnswerIs 6) :=
  by 
    repeat constructor
    done

  example : 2 + 3 = 5 := by simp
    
-- -------------- Transition Relation ---------------------
structure trsys (state) := 
    (initial : state → Prop)
    (step : state → state → Prop)
-- -------------- Transition Relation ---------------------

def factorial_sys (original_input : ℕ) : trsys fact_state := {
    initial := fact_init original_input,
    step := fact_step
  }

-- -------------- Transition Relation ---------------------
inductive reachable {state} (sys : trsys state) (st : state) : Prop :=
  | Reachable : ∀ st0, sys.initial st0 -> sys.step^* st0 st -> reachable sys st

def invariantFor {state} (sys : trsys state) (invariant : state → Prop) :=
  ∀ s, sys.initial s → ∀ s', sys.step^* s s' → invariant s'
    
theorem use_invariant' : ∀ {state} (sys : trsys state) 
  (invariant : state → Prop) s s',
  invariantFor sys invariant 
  → sys.initial s 
  → sys.step^* s s'
  → invariant s' := by
  -- intros state trsys inv s s'
  simp [invariantFor]
  intros _ _ _ _ _ H _ _ 
  apply H
  assumption
  assumption

theorem use_invariant : ∀ {state} (sys : trsys state)
  (invariant : state → Prop) s,
  invariantFor sys invariant → reachable sys s → invariant s := by
  intros _ _ _ _ _ H0
  cases H0 
  apply use_invariant'
  repeat assumption
  
theorem invariant_induction' : ∀ {state} (sys : trsys state)
  (invariant : state → Prop),
  (∀ s, invariant s → ∀ s', sys.step s s' → invariant s')
  → ∀ s s', sys.step^* s s'
    → invariant s
    → invariant s' := by
  intros _ _ _ H₀ _ _ H₁
  induction H₁ with
  | TrcRefl a => 
    intro
    assumption
  | TrcFront _ _ _ _ _ iH => 
    intros
    apply iH
    apply H₀
    repeat assumption
    done

theorem invariant_induction : ∀ {state} (sys : trsys state) 
  (invariant : state → Prop),
  (∀ s, sys.initial s → invariant s)
  → (∀ s, invariant s → ∀ s', sys.step s s' → invariant s')
  → invariantFor sys invariant := by
  simp [invariantFor]; intros _ _ _ H _ _ _ _ _ 
  apply invariant_induction'
  assumption
  assumption
  apply H 
  assumption

-- -------------- Transition Relation --------------------- 
open fact_state
def fact_invariant (original_input : ℕ) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator n acc => fact original_input = fact n * acc
  
theorem fact_invariant_ok : ∀ original_input,
  invariantFor (factorial_sys original_input) (fact_invariant original_input) := by
  intros oi
  apply invariant_induction
  intros s 
  simp [factorial_sys]
  intro H
  cases H
  simp [fact_invariant]
  intros s
  simp [factorial_sys]
  intros H _ H0
  cases H0
  
  simp [fact_invariant, fact] at *
  assumption

  simp [fact_invariant, fact] at *
  rw [H, Nat.mul_assoc]
  simp [Nat.mul_comm]
  done 

theorem fact_invariant_always : ∀ original_input s,
  reachable (factorial_sys original_input) s
  → fact_invariant original_input s := by
  intros 
  apply use_invariant
  apply fact_invariant_ok
  assumption

--  Therefore, any final state has the right answer! 
theorem fact_ok' : ∀ original_input s,
  fact_final s
  -> fact_invariant original_input s
  -> s = AnswerIs (fact original_input)
:= by
  intros oi s
  simp [fact_invariant] at *
  cases s with 
  | AnswerIs x => 
    simp
    intros a b
    rw [b]
    done
  | WithAccumulator => 
    simp 
    intros H 
    cases H
    done
  
theorem fact_ok : ∀ original_input s,
  reachable (factorial_sys original_input) s 
  → fact_final s
  → s = AnswerIs (fact original_input) := by
  intros
  apply fact_ok'
  assumption
  apply fact_invariant_always
  assumption
  done


  




  

def main : IO Unit :=
  IO.println  (fact 4)
