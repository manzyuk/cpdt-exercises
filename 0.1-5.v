Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive even_nat : Set :=
| EO : even_nat
| ES : odd_nat -> even_nat
with odd_nat : Set :=
| OS : even_nat -> odd_nat.

Fixpoint even_plus (en1 en2 : even_nat) : even_nat :=
  match en1 with
  | EO => en2
  | ES on => ES (odd_plus on en2)
  end
with odd_plus (on : odd_nat) (en : even_nat) : odd_nat :=
  match on with
  | OS en' => OS (even_plus en' en)
  end.

Scheme even_nat_mut := Induction for even_nat Sort Prop
  with odd_nat_mut := Induction for odd_nat Sort Prop.

Check even_nat_mut.

Lemma even_plus_EO : forall (en : even_nat), even_plus en EO = en.
  apply (even_nat_mut
           (fun en : even_nat => even_plus en EO = en)
           (fun on : odd_nat => odd_plus on EO = on)); crush.
Qed.

Lemma even_plus_ES : forall (en1 en2 : even_nat),
    ES (OS (even_plus en1 en2)) = even_plus en1 (ES (OS en2)).
  apply (even_nat_mut
           (fun en1 : even_nat => forall en2 : even_nat,
                ES (OS (even_plus en1 en2)) = even_plus en1 (ES (OS en2)))
           (fun on : odd_nat => forall en : even_nat,
                OS (ES (odd_plus on en)) = odd_plus on (ES (OS en)))); crush.
Qed.

Hint Rewrite even_plus_EO.
Hint Rewrite even_plus_ES.

Theorem even_plus_comm : forall (en1 en2 : even_nat),
    even_plus en1 en2 = even_plus en2 en1.
  apply (even_nat_mut
           (fun en1 : even_nat => forall en2 : even_nat,
                even_plus en1 en2 = even_plus en2 en1)
           (fun on : odd_nat => forall en : even_nat,
                ES (odd_plus on en) = even_plus en (ES on))); crush.
Qed.
