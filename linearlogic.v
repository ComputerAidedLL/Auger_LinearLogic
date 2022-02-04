(** Linear Logic in Coq *)
Require Import Utf8_core.
Require Import List.
Set Implicit Arguments.
Inductive linear_expression: Prop :=
| D: ∀ (is_positive: bool)
       (absolute_value: expression)
, linear_expression
with expression: Prop :=
| A: ∀ (atom: Prop)
, expression
| B: ∀ (left_expression: linear_expression)
       (is_multiplicative: bool)
       (right_expression: linear_expression)
, expression
| C: ∀ (is_multiplicative: bool)
, expression
| E: ∀ (delayed_expression: linear_expression)
, expression
.
Notation "a ⊗ b" := (D true (B a true b)) (at level 30).
Notation "a & b" := (D false (B a false b)) (at level 40).
Notation "a ⊕ b" := (D true (B a false b)) (at level 50).
Notation "a ⅋ b" := (D false (B a true b)) (at level 60).
Notation "𝟘" := (D true (C false)).
Notation "𝟙" := (D true (C true)).
Notation "⊥" := (D false (C true)).
Notation "⊤" := (D false (C false)).
Notation "! a" := (D true (E a)) (at level 20).
Notation "? a" := (D false (E a)) (at level 20).
Notation "a ⁺" := (D true (A a)) (at level 10, format "a ⁺").
Notation "a ⁻" := (D false (A a)) (at level 10, format "a ⁻").
Example formula (A: Prop) := (?⊥⊕A⁻)⊗!(𝟙&𝟘⅋⊤).
Eval compute in (formula (0>1)).
Fixpoint linear_dual (e: linear_expression) :=
 match e with
 | D pos abs => D (if pos then false else true) (dual abs)
 end
 with dual e :=
 match e with
 | B l m r => B (linear_dual l) m (linear_dual r)
 | E l => E (linear_dual l)
 | _ => e
 end.
Notation "a ⁽⁻⁾" := (linear_dual a) (at level 10).
Eval compute in (λ (P: Prop), (formula P)⁽⁻⁾).
Theorem linear_dual_idempotent: ∀ φ, φ = φ⁽⁻⁾⁽⁻⁾
with dual_idempotent: ∀ ψ, ψ = dual (dual ψ).
  Proof.
  intros [positivity absolute]; simpl.
  case dual_idempotent; case positivity; split.
 Proof.
 intros []; simpl; intros; repeat case linear_dual_idempotent; split.
Qed.
Fixpoint split i (lst: list linear_expression) :=
 match i with
 | O => (nil, lst)
 |S i=> match lst with
        |  nil  => (nil, nil)
        |le::lst=> let (l, r) := split i lst in (le::l, r)
        end
 end.
Inductive all_delayed: list linear_expression → Prop :=
| NoMoreDelays: all_delayed nil
| MoreDelays: ∀ l, all_delayed l → ∀ le, all_delayed (? le::l).
Inductive three_choices: Set := Birth | Life | Death.
Definition why_choice t le :=
 match t with
 | Birth => nil
 | Life => le::nil
 | Death => ? le::? le::nil
 end.
Inductive provable: list linear_expression → Prop :=
| Move: ∀ n l, provable (let (l, r) := split n l in r++l) → provable l
| Atom: ∀ P, provable (P⁺::P⁻::nil)
| Times: ∀ n lst a b, provable (a::(fst (split n lst))) →
                      provable (b::(snd (split n lst))) →
                      provable (a⊗b::lst)
| With: ∀ l a b, provable (a::l) → provable (b::l) → provable (a&b::l)
| Plus: ∀ l a b (c: bool),
        provable ((if c then a else b)::l) → provable (a⊕b::l)
| Par: ∀ l a b, provable (a::b::l) → provable (a⅋b::l)
| One: provable (𝟙::nil)
| Bottom: ∀ l, provable l → provable (⊥::l)
| Top: ∀ l, provable (⊤::l)
| Bang: ∀ l, all_delayed l → ∀ le, provable (le::l) → provable (! le::l)
| Wnot: ∀ l t le, provable ((why_choice t le)++l) → provable (? le::l)
| Cut: ∀ t n lst, provable (t::(fst (split n lst))) →
                  provable (linear_dual t::(snd (split n lst))) →
                  provable lst.
Definition stack tl := List.map linear_dual tl.
Inductive these_provable hd tl : Prop :=
ProvableWrapper: provable (hd::(stack tl)) →
                 these_provable hd tl.
Notation "∗ H1 .. H2 ⊢ J" :=
 (these_provable J (H1::..(H2::nil)..))
 (at level 100, format
  "'[v' ∗ '/' H1 '/' .. '/' H2 '/' ']' ⊢ J"
 ).
Notation "∗ ⊢ J" :=
 (these_provable J nil)
 (at level 100, format
  "'[v' ∗ '/' ']' ⊢ J"
 ).
Tactic Notation "linear" tactic(tac) :=
apply ProvableWrapper;
simpl;
tac;
simpl;
let H := fresh in
match goal with
| |- provable (?hd::?tl) =>
  cut (these_provable hd (stack tl)); simpl;
  [now intros [H]; revert H; simpl; clear;
   repeat case linear_dual_idempotent
  |repeat case linear_dual_idempotent]
end.
Ltac move_ n :=
apply Move with n.
Ltac times_ n :=
apply Times with n.
Ltac left_ :=
apply Plus with true.
Ltac right_ :=
apply Plus with false.
Ltac bang_ :=
apply Bang; [simpl; repeat constructor|].
Ltac weak_ :=
apply Wnot with Birth.
Ltac derel_ :=
apply Wnot with Life.
Ltac contr_ :=
apply Wnot with Death.
Ltac cut_ t n :=
apply Cut with t n.
Lemma linear_em: ∀ φ, ∗φ⊢φ
with lem: ∀ ψ b, ∗D b ψ ⊢ D b ψ.
  Proof.
  clear -lem; intros [b ψ].
  apply lem.
 Proof.
 clear lem; intros [a|φ₁ μ φ₂|[]|φ];
 ((assert (Φ₁ := linear_em φ₁); assert (Φ₂ := linear_em φ₂))
||(assert (Φ := linear_em φ))
||idtac); (try case μ); intros []; simpl; clear linear_em.
            now linear constructor.
           linear move_ 1.
           now linear constructor.
          linear move_ 1.
          linear constructor; move_ 2.
          now linear times_ 1.
         linear constructor; move_ 2.
         now linear times_ 1; move_ 1.
        linear move_ 1.
        linear constructor; move_ 1.
         now linear left_.
        now linear right_.
       linear constructor; move_ 1.
        now linear left_; move_ 1.
       now linear right_; move_ 1.
      linear move_ 1.
      now linear repeat constructor.
     now linear repeat constructor.
    linear move_ 1.
    now linear constructor.
   now linear constructor.
  linear bang_; move_ 1.
  now linear derel_; move_ 1.
 linear move_ 1.
 linear bang_; move_ 1.
 now linear derel_.
Qed.
Goal ∀ φ, ∗ ⊢φ⁽⁻⁾⅋φ.
 intro φ.
 linear constructor.
 apply linear_em.
Qed.
