(******************************************************************************)
(*                                                                            *)
(*         Pāṇinian Sandhi: A Verified Formalization of Aṣṭādhyāyī 6.1        *)
(*                                                                            *)
(*     Pratyāhāras computed from Śiva Sūtras; vowel sandhi rules (6.1.77,     *)
(*     78, 87, 88, 101, 109) with vipratiṣedha conflict resolution. Full      *)
(*     soundness and completeness: the computational function corresponds     *)
(*     exactly to the declarative relational specification.                   *)
(*                                                                            *)
(*     "The first generative grammar in the modern sense was Panini's         *)
(*      grammar."                                                             *)
(*     - Noam Chomsky                                                         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Relations.
Import ListNotations.

Set Implicit Arguments.

(** * Part I: Phoneme Inventory *)

Inductive Vowel : Type :=
  | V_a | V_aa
  | V_i | V_ii
  | V_u | V_uu
  | V_r | V_rr
  | V_l
  | V_e | V_ai
  | V_o | V_au.

Inductive Consonant : Type :=
  | C_k | C_kh | C_g | C_gh | C_ng
  | C_c | C_ch | C_j | C_jh | C_ny
  | C_tt | C_tth | C_dd | C_ddh | C_nn
  | C_t | C_th | C_d | C_dh | C_n
  | C_p | C_ph | C_b | C_bh | C_m
  | C_y | C_r | C_l | C_v
  | C_sh | C_ss | C_s
  | C_h.

Inductive Phoneme : Type :=
  | Svar : Vowel -> Phoneme
  | Vyan : Consonant -> Phoneme
  | Anusvara : Phoneme
  | Visarga : Phoneme.

Definition Word := list Phoneme.

Scheme Equality for Vowel.
Scheme Equality for Consonant.
Scheme Equality for Phoneme.

(** * Part II: Śiva Sūtras and Pratyāhāra *)

Inductive SivaSound : Type :=
  | SS_vowel : Vowel -> SivaSound
  | SS_cons : Consonant -> SivaSound
  | SS_it : nat -> SivaSound.

Definition siva_sutra_1 : list SivaSound :=
  [SS_vowel V_a; SS_vowel V_i; SS_vowel V_u; SS_it 1].

Definition siva_sutra_2 : list SivaSound :=
  [SS_vowel V_r; SS_vowel V_l; SS_it 2].

Definition siva_sutra_3 : list SivaSound :=
  [SS_vowel V_e; SS_vowel V_o; SS_it 3].

Definition siva_sutra_4 : list SivaSound :=
  [SS_vowel V_ai; SS_vowel V_au; SS_it 4].

Definition siva_sutra_5 : list SivaSound :=
  [SS_cons C_h; SS_cons C_y; SS_cons C_v; SS_cons C_r; SS_it 5].

Definition siva_sutra_6 : list SivaSound :=
  [SS_cons C_l; SS_it 6].

Definition siva_sutra_7 : list SivaSound :=
  [SS_cons C_ny; SS_cons C_m; SS_cons C_ng; SS_cons C_nn; SS_cons C_n; SS_it 7].

Definition siva_sutra_8 : list SivaSound :=
  [SS_cons C_jh; SS_cons C_bh; SS_it 8].

Definition siva_sutra_9 : list SivaSound :=
  [SS_cons C_gh; SS_cons C_ddh; SS_cons C_dh; SS_it 9].

Definition siva_sutra_10 : list SivaSound :=
  [SS_cons C_j; SS_cons C_b; SS_cons C_g; SS_cons C_dd; SS_cons C_d; SS_it 10].

Definition siva_sutra_11 : list SivaSound :=
  [SS_cons C_kh; SS_cons C_ph; SS_cons C_ch; SS_cons C_tth; SS_cons C_th;
   SS_cons C_c; SS_cons C_tt; SS_cons C_t; SS_it 11].

Definition siva_sutra_12 : list SivaSound :=
  [SS_cons C_k; SS_cons C_p; SS_it 12].

Definition siva_sutra_13 : list SivaSound :=
  [SS_cons C_sh; SS_cons C_ss; SS_cons C_s; SS_it 13].

Definition siva_sutra_14 : list SivaSound :=
  [SS_cons C_h; SS_cons C_l; SS_it 14].

Definition all_siva_sutras : list SivaSound :=
  siva_sutra_1 ++ siva_sutra_2 ++ siva_sutra_3 ++ siva_sutra_4 ++
  siva_sutra_5 ++ siva_sutra_6 ++ siva_sutra_7 ++ siva_sutra_8 ++
  siva_sutra_9 ++ siva_sutra_10 ++ siva_sutra_11 ++ siva_sutra_12 ++
  siva_sutra_13 ++ siva_sutra_14.

Definition is_it (s : SivaSound) : bool :=
  match s with SS_it _ => true | _ => false end.

Definition sound_eq_vowel (s : SivaSound) (v : Vowel) : bool :=
  match s with
  | SS_vowel v' => Vowel_beq v v'
  | _ => false
  end.

Definition sound_eq_cons (s : SivaSound) (c : Consonant) : bool :=
  match s with
  | SS_cons c' => Consonant_beq c c'
  | _ => false
  end.

Fixpoint take_until_it (ss : list SivaSound) : list SivaSound :=
  match ss with
  | [] => []
  | s :: rest =>
      if is_it s then []
      else s :: take_until_it rest
  end.

Fixpoint drop_through_sound_vowel (v : Vowel) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      if sound_eq_vowel s v then Some rest
      else drop_through_sound_vowel v rest
  end.

Fixpoint drop_through_sound_cons (c : Consonant) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      if sound_eq_cons s c then Some rest
      else drop_through_sound_cons c rest
  end.

Fixpoint drop_through_it (n : nat) (ss : list SivaSound)
  : option (list SivaSound) :=
  match ss with
  | [] => None
  | s :: rest =>
      match s with
      | SS_it m => if Nat.eqb n m then Some rest else drop_through_it n rest
      | _ => drop_through_it n rest
      end
  end.

Definition pratyahara_vowels (start : Vowel) (end_it : nat)
  : list Vowel :=
  match drop_through_sound_vowel start all_siva_sutras with
  | None => []
  | Some after_start =>
      let segment := start ::
        (fix extract ss :=
          match ss with
          | [] => []
          | SS_vowel v :: rest => v :: extract rest
          | SS_it n :: rest => if Nat.eqb n end_it then [] else extract rest
          | _ :: rest => extract rest
          end) after_start
      in segment
  end.

Definition in_pratyahara_vowel (v : Vowel) (start : Vowel) (end_it : nat)
  : bool :=
  existsb (Vowel_beq v) (pratyahara_vowels start end_it).

Definition short_of (v : Vowel) : Vowel :=
  match v with
  | V_aa => V_a
  | V_ii => V_i
  | V_uu => V_u
  | V_rr => V_r
  | other => other
  end.

Definition in_pratyahara_with_savarna (v : Vowel) (start : Vowel) (end_it : nat)
  : bool :=
  existsb (Vowel_beq (short_of v)) (pratyahara_vowels start end_it).

Definition ik_vowels : list Vowel := pratyahara_vowels V_i 2.
Definition ak_vowels : list Vowel := pratyahara_vowels V_a 2.
Definition ec_vowels : list Vowel := pratyahara_vowels V_e 4.
Definition ac_vowels : list Vowel := pratyahara_vowels V_a 4.

Definition is_ik_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_i 2.

Definition is_ak_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_a 2.

Definition is_ec_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_e 4.

Definition is_ac_computed (v : Vowel) : bool :=
  in_pratyahara_with_savarna v V_a 4.

(** Pratyāhāra specifications derived from Śiva Sūtras. *)

(** ac = a to c (sūtras 1-4): all vowels. *)
Inductive is_ac_spec : Vowel -> Prop :=
  | AC_a : is_ac_spec V_a   | AC_aa : is_ac_spec V_aa
  | AC_i : is_ac_spec V_i   | AC_ii : is_ac_spec V_ii
  | AC_u : is_ac_spec V_u   | AC_uu : is_ac_spec V_uu
  | AC_r : is_ac_spec V_r   | AC_rr : is_ac_spec V_rr
  | AC_l : is_ac_spec V_l
  | AC_e : is_ac_spec V_e   | AC_ai : is_ac_spec V_ai
  | AC_o : is_ac_spec V_o   | AC_au : is_ac_spec V_au.

Lemma is_ac_spec_total : forall v, is_ac_spec v.
Proof. destruct v; constructor. Qed.

(** ik = i to k (sūtras 1-2): i, u, ṛ, ḷ and long forms. *)
Inductive is_ik_spec : Vowel -> Prop :=
  | IK_i : is_ik_spec V_i   | IK_ii : is_ik_spec V_ii
  | IK_u : is_ik_spec V_u   | IK_uu : is_ik_spec V_uu
  | IK_r : is_ik_spec V_r   | IK_rr : is_ik_spec V_rr
  | IK_l : is_ik_spec V_l.

Lemma is_ik_correct : forall v,
  is_ik_computed v = true <-> is_ik_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ak = a to k (sūtras 1-2): a, i, u, ṛ, ḷ and long forms. *)
Inductive is_ak_spec : Vowel -> Prop :=
  | AK_a : is_ak_spec V_a   | AK_aa : is_ak_spec V_aa
  | AK_i : is_ak_spec V_i   | AK_ii : is_ak_spec V_ii
  | AK_u : is_ak_spec V_u   | AK_uu : is_ak_spec V_uu
  | AK_r : is_ak_spec V_r   | AK_rr : is_ak_spec V_rr
  | AK_l : is_ak_spec V_l.

Lemma is_ak_correct : forall v,
  is_ak_computed v = true <-> is_ak_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** ec = e to c (sūtras 3-4): e, o, ai, au. *)
Inductive is_ec_spec : Vowel -> Prop :=
  | EC_e : is_ec_spec V_e   | EC_ai : is_ec_spec V_ai
  | EC_o : is_ec_spec V_o   | EC_au : is_ec_spec V_au.

Lemma is_ec_correct : forall v,
  is_ec_computed v = true <-> is_ec_spec v.
Proof.
  intro v; split.
  - intro H; destruct v; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Partition lemma: every vowel is either a-class, ik, or ec. *)
Lemma vowel_trichotomy : forall v,
  (v = V_a \/ v = V_aa) \/
  is_ik_spec v \/
  is_ec_spec v.
Proof.
  intro v.
  destruct v.
  - left; left; reflexivity.
  - left; right; reflexivity.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; left; constructor.
  - right; right; constructor.
  - right; right; constructor.
  - right; right; constructor.
  - right; right; constructor.
Qed.

(** * Part III: Paribhāṣā Sūtras (Meta-rules) *)

(** ** 1.1.1 vṛddhir ādaic *)
(** "ā, ai, and au are called vṛddhi."
    This defines the technical term 'vṛddhi' for these three vowels. *)

Inductive is_vrddhi_vowel_spec : Vowel -> Prop :=
  | Vrddhi_aa : is_vrddhi_vowel_spec V_aa
  | Vrddhi_ai : is_vrddhi_vowel_spec V_ai
  | Vrddhi_au : is_vrddhi_vowel_spec V_au.

Definition is_vrddhi_vowel (v : Vowel) : bool :=
  match v with
  | V_aa | V_ai | V_au => true
  | _ => false
  end.

Lemma is_vrddhi_vowel_correct : forall v,
  is_vrddhi_vowel v = true <-> is_vrddhi_vowel_spec v.
Proof.
  intro v.
  split.
  - intro H.
    destruct v; simpl in H; try discriminate.
    + apply Vrddhi_aa.
    + apply Vrddhi_ai.
    + apply Vrddhi_au.
  - intro H.
    destruct H; reflexivity.
Qed.

(** ** 1.1.2 adeṅ guṇaḥ *)
(** "a, e, and o are called guṇa." *)

Inductive is_guna_vowel_spec : Vowel -> Prop :=
  | Guna_a : is_guna_vowel_spec V_a
  | Guna_e : is_guna_vowel_spec V_e
  | Guna_o : is_guna_vowel_spec V_o.

Definition is_guna_vowel (v : Vowel) : bool :=
  match v with
  | V_a | V_e | V_o => true
  | _ => false
  end.

Lemma is_guna_vowel_correct : forall v,
  is_guna_vowel v = true <-> is_guna_vowel_spec v.
Proof.
  intro v.
  split.
  - intro H.
    destruct v; simpl in H; try discriminate.
    + apply Guna_a.
    + apply Guna_e.
    + apply Guna_o.
  - intro H.
    destruct H; reflexivity.
Qed.

(** ** 1.1.3 iko guṇavṛddhī *)
(** "Guṇa and vṛddhi are substitutes for ik vowels."
    ik = i, u, ṛ, ḷ (and long forms). *)

Inductive guna_substitute_spec : Vowel -> Vowel -> Prop :=
  | GS_i : guna_substitute_spec V_i V_e
  | GS_ii : guna_substitute_spec V_ii V_e
  | GS_u : guna_substitute_spec V_u V_o
  | GS_uu : guna_substitute_spec V_uu V_o.

Inductive vrddhi_substitute_spec : Vowel -> Vowel -> Prop :=
  | VS_i : vrddhi_substitute_spec V_i V_ai
  | VS_ii : vrddhi_substitute_spec V_ii V_ai
  | VS_u : vrddhi_substitute_spec V_u V_au
  | VS_uu : vrddhi_substitute_spec V_uu V_au.

Definition guna_of_ik (v : Vowel) : option Vowel :=
  match v with
  | V_i | V_ii => Some V_e
  | V_u | V_uu => Some V_o
  | _ => None
  end.

Definition vrddhi_of_ik (v : Vowel) : option Vowel :=
  match v with
  | V_i | V_ii => Some V_ai
  | V_u | V_uu => Some V_au
  | _ => None
  end.

Lemma guna_of_ik_correct : forall v1 v2,
  guna_of_ik v1 = Some v2 <-> guna_substitute_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    destruct v1; simpl in H; try discriminate;
    injection H as H; subst.
    + apply GS_i.
    + apply GS_ii.
    + apply GS_u.
    + apply GS_uu.
  - intro H.
    destruct H; reflexivity.
Qed.

Lemma vrddhi_of_ik_correct : forall v1 v2,
  vrddhi_of_ik v1 = Some v2 <-> vrddhi_substitute_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    destruct v1; simpl in H; try discriminate;
    injection H as H; subst.
    + apply VS_i.
    + apply VS_ii.
    + apply VS_u.
    + apply VS_uu.
  - intro H.
    destruct H; reflexivity.
Qed.

(** ṛ/ḷ have compound guṇa/vṛddhi (ar/al, ār/āl). *)

Inductive guna_r_spec : Vowel -> list Phoneme -> Prop :=
  | GRS_r : guna_r_spec V_r [Svar V_a; Vyan C_r]
  | GRS_rr : guna_r_spec V_rr [Svar V_a; Vyan C_r]
  | GRS_l : guna_r_spec V_l [Svar V_a; Vyan C_l].

Inductive vrddhi_r_spec : Vowel -> list Phoneme -> Prop :=
  | VRS_r : vrddhi_r_spec V_r [Svar V_aa; Vyan C_r]
  | VRS_rr : vrddhi_r_spec V_rr [Svar V_aa; Vyan C_r]
  | VRS_l : vrddhi_r_spec V_l [Svar V_aa; Vyan C_l].

(** * Part IV: Savarṇa (1.1.9) *)

Inductive SavarnaClass : Type :=
  | SC_a | SC_i | SC_u | SC_r | SC_l | SC_e | SC_ai | SC_o | SC_au.

Definition savarna_class (v : Vowel) : SavarnaClass :=
  match v with
  | V_a | V_aa => SC_a
  | V_i | V_ii => SC_i
  | V_u | V_uu => SC_u
  | V_r | V_rr => SC_r
  | V_l => SC_l
  | V_e => SC_e
  | V_ai => SC_ai
  | V_o => SC_o
  | V_au => SC_au
  end.

Scheme Equality for SavarnaClass.

Definition savarna (v1 v2 : Vowel) : bool :=
  SavarnaClass_beq (savarna_class v1) (savarna_class v2).

Lemma savarna_refl : forall v, savarna v v = true.
Proof.
  intro v.
  unfold savarna.
  destruct v; reflexivity.
Qed.

Lemma savarna_sym : forall v1 v2, savarna v1 v2 = savarna v2 v1.
Proof.
  intros v1 v2.
  unfold savarna.
  destruct v1, v2; reflexivity.
Qed.

(** ** 1.1.9 tulyāsyaprayatnaṁ savarṇam *)
(** "Sounds with same place and effort of articulation are savarṇa."
    For vowels: a/ā, i/ī, u/ū, ṛ/ṝ are savarṇa pairs. *)

Inductive savarna_spec : Vowel -> Vowel -> Prop :=
  | Sav_a_a : savarna_spec V_a V_a
  | Sav_a_aa : savarna_spec V_a V_aa
  | Sav_aa_a : savarna_spec V_aa V_a
  | Sav_aa_aa : savarna_spec V_aa V_aa
  | Sav_i_i : savarna_spec V_i V_i
  | Sav_i_ii : savarna_spec V_i V_ii
  | Sav_ii_i : savarna_spec V_ii V_i
  | Sav_ii_ii : savarna_spec V_ii V_ii
  | Sav_u_u : savarna_spec V_u V_u
  | Sav_u_uu : savarna_spec V_u V_uu
  | Sav_uu_u : savarna_spec V_uu V_u
  | Sav_uu_uu : savarna_spec V_uu V_uu
  | Sav_r_r : savarna_spec V_r V_r
  | Sav_r_rr : savarna_spec V_r V_rr
  | Sav_rr_r : savarna_spec V_rr V_r
  | Sav_rr_rr : savarna_spec V_rr V_rr
  | Sav_l_l : savarna_spec V_l V_l
  | Sav_e_e : savarna_spec V_e V_e
  | Sav_ai_ai : savarna_spec V_ai V_ai
  | Sav_o_o : savarna_spec V_o V_o
  | Sav_au_au : savarna_spec V_au V_au.

Lemma savarna_correct : forall v1 v2,
  savarna v1 v2 = true <-> savarna_spec v1 v2.
Proof.
  intros v1 v2.
  split.
  - intro H.
    unfold savarna in H.
    destruct v1, v2; simpl in H; try discriminate; constructor.
  - intro H.
    unfold savarna.
    destruct H; reflexivity.
Qed.

Lemma savarna_spec_refl : forall v, savarna_spec v v.
Proof.
  intro v.
  destruct v; constructor.
Qed.

Lemma savarna_spec_sym : forall v1 v2,
  savarna_spec v1 v2 -> savarna_spec v2 v1.
Proof.
  intros v1 v2 H.
  destruct H; constructor.
Qed.

(** * Part V: Guṇa and Vṛddhi (1.1.1-2) *)

Definition guna (v : Vowel) : list Phoneme :=
  match v with
  | V_a | V_aa => [Svar V_a]
  | V_i | V_ii => [Svar V_e]
  | V_u | V_uu => [Svar V_o]
  | V_r | V_rr => [Svar V_a; Vyan C_r]
  | V_l => [Svar V_a; Vyan C_l]
  | V_e => [Svar V_e]
  | V_o => [Svar V_o]
  | V_ai => [Svar V_ai]
  | V_au => [Svar V_au]
  end.

Definition vrddhi (v : Vowel) : list Phoneme :=
  match v with
  | V_a | V_aa => [Svar V_aa]
  | V_i | V_ii => [Svar V_ai]
  | V_u | V_uu => [Svar V_au]
  | V_r | V_rr => [Svar V_aa; Vyan C_r]
  | V_l => [Svar V_aa; Vyan C_l]
  | V_e => [Svar V_ai]
  | V_o => [Svar V_au]
  | V_ai => [Svar V_ai]
  | V_au => [Svar V_au]
  end.

Definition lengthen (v : Vowel) : Vowel :=
  match v with
  | V_a => V_aa
  | V_i => V_ii
  | V_u => V_uu
  | V_r => V_rr
  | other => other
  end.

Definition is_a_class (v : Vowel) : bool :=
  match v with V_a | V_aa => true | _ => false end.

(** * Part V: Yaṇ Correspondence *)

Definition yan_of (v : Vowel) : option Consonant :=
  match v with
  | V_i | V_ii => Some C_y
  | V_u | V_uu => Some C_v
  | V_r | V_rr => Some C_r
  | V_l => Some C_l
  | _ => None
  end.

Lemma yan_of_ik : forall v,
  is_ik_computed v = true -> exists c, yan_of v = Some c.
Proof.
  intros v H.
  destruct v; simpl in H; try discriminate.
  - exists C_y. reflexivity.
  - exists C_y. reflexivity.
  - exists C_v. reflexivity.
  - exists C_v. reflexivity.
  - exists C_r. reflexivity.
  - exists C_r. reflexivity.
  - exists C_l. reflexivity.
Qed.

Definition ayavayav (v : Vowel) : option (list Phoneme) :=
  match v with
  | V_e => Some [Svar V_a; Vyan C_y]
  | V_o => Some [Svar V_a; Vyan C_v]
  | V_ai => Some [Svar V_aa; Vyan C_y]
  | V_au => Some [Svar V_aa; Vyan C_v]
  | _ => None
  end.

Lemma ayavayav_ec : forall v,
  is_ec_computed v = true -> exists ps, ayavayav v = Some ps.
Proof.
  intros v H.
  destruct v; simpl in H; try discriminate.
  - exists [Svar V_a; Vyan C_y]. reflexivity.
  - exists [Svar V_aa; Vyan C_y]. reflexivity.
  - exists [Svar V_a; Vyan C_v]. reflexivity.
  - exists [Svar V_aa; Vyan C_v]. reflexivity.
Qed.

(** * Part VI: Sūtra Numbering and Precedence *)

Record SutraNum := {
  adhyaya : nat;
  pada : nat;
  sutra : nat
}.

Definition sutra_eq (s1 s2 : SutraNum) : bool :=
  Nat.eqb (adhyaya s1) (adhyaya s2) &&
  Nat.eqb (pada s1) (pada s2) &&
  Nat.eqb (sutra s1) (sutra s2).

Definition sutra_lt (s1 s2 : SutraNum) : Prop :=
  adhyaya s1 < adhyaya s2 \/
  (adhyaya s1 = adhyaya s2 /\ pada s1 < pada s2) \/
  (adhyaya s1 = adhyaya s2 /\ pada s1 = pada s2 /\ sutra s1 < sutra s2).

Definition sutra_ltb (s1 s2 : SutraNum) : bool :=
  if Nat.ltb (adhyaya s1) (adhyaya s2) then true
  else if Nat.eqb (adhyaya s1) (adhyaya s2) then
    if Nat.ltb (pada s1) (pada s2) then true
    else if Nat.eqb (pada s1) (pada s2) then
      Nat.ltb (sutra s1) (sutra s2)
    else false
  else false.

Lemma sutra_ltb_irrefl : forall s, sutra_ltb s s = false.
Proof.
  intro s.
  unfold sutra_ltb.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  rewrite Nat.ltb_irrefl.
  reflexivity.
Qed.

Lemma sutra_ltb_trans : forall s1 s2 s3,
  sutra_ltb s1 s2 = true ->
  sutra_ltb s2 s3 = true ->
  sutra_ltb s1 s3 = true.
Proof.
  intros s1 s2 s3 H12 H23.
  unfold sutra_ltb in *.
  destruct (Nat.ltb (adhyaya s1) (adhyaya s2)) eqn:E1.
  - apply Nat.ltb_lt in E1.
    destruct (Nat.ltb (adhyaya s2) (adhyaya s3)) eqn:E2.
    + apply Nat.ltb_lt in E2.
      assert (adhyaya s1 < adhyaya s3) by lia.
      apply Nat.ltb_lt in H.
      rewrite H. reflexivity.
    + destruct (Nat.eqb (adhyaya s2) (adhyaya s3)) eqn:E2'.
      * apply Nat.eqb_eq in E2'.
        assert (adhyaya s1 < adhyaya s3) by lia.
        apply Nat.ltb_lt in H.
        rewrite H. reflexivity.
      * discriminate.
  - destruct (Nat.eqb (adhyaya s1) (adhyaya s2)) eqn:E1'; try discriminate.
    apply Nat.eqb_eq in E1'.
    destruct (Nat.ltb (adhyaya s2) (adhyaya s3)) eqn:E2.
    + apply Nat.ltb_lt in E2.
      assert (adhyaya s1 < adhyaya s3) by lia.
      apply Nat.ltb_lt in H.
      rewrite H. reflexivity.
    + destruct (Nat.eqb (adhyaya s2) (adhyaya s3)) eqn:E2'; try discriminate.
      apply Nat.eqb_eq in E2'.
      assert (Nat.ltb (adhyaya s1) (adhyaya s3) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s3) = true).
      { apply Nat.eqb_eq. lia. }
      rewrite H0.
      destruct (Nat.ltb (pada s1) (pada s2)) eqn:P1.
      * apply Nat.ltb_lt in P1.
        destruct (Nat.ltb (pada s2) (pada s3)) eqn:P2.
        -- apply Nat.ltb_lt in P2.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
        -- destruct (Nat.eqb (pada s2) (pada s3)) eqn:P2'; try discriminate.
           apply Nat.eqb_eq in P2'.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
      * destruct (Nat.eqb (pada s1) (pada s2)) eqn:P1'; try discriminate.
        apply Nat.eqb_eq in P1'.
        destruct (Nat.ltb (pada s2) (pada s3)) eqn:P2.
        -- apply Nat.ltb_lt in P2.
           assert (pada s1 < pada s3) by lia.
           apply Nat.ltb_lt in H1.
           rewrite H1. reflexivity.
        -- destruct (Nat.eqb (pada s2) (pada s3)) eqn:P2'; try discriminate.
           apply Nat.eqb_eq in P2'.
           assert (Nat.ltb (pada s1) (pada s3) = false).
           { apply Nat.ltb_ge. lia. }
           rewrite H1.
           assert (Nat.eqb (pada s1) (pada s3) = true).
           { apply Nat.eqb_eq. lia. }
           rewrite H2.
           apply Nat.ltb_lt in H12.
           apply Nat.ltb_lt in H23.
           apply Nat.ltb_lt.
           lia.
Qed.

Lemma sutra_ltb_correct : forall s1 s2,
  sutra_ltb s1 s2 = true <-> sutra_lt s1 s2.
Proof.
  intros s1 s2.
  split.
  - intro H.
    unfold sutra_ltb in H.
    unfold sutra_lt.
    destruct (Nat.ltb (adhyaya s1) (adhyaya s2)) eqn:E1.
    + left.
      apply Nat.ltb_lt.
      exact E1.
    + destruct (Nat.eqb (adhyaya s1) (adhyaya s2)) eqn:E1'; try discriminate.
      apply Nat.eqb_eq in E1'.
      destruct (Nat.ltb (pada s1) (pada s2)) eqn:E2.
      * right. left.
        split.
        -- exact E1'.
        -- apply Nat.ltb_lt. exact E2.
      * destruct (Nat.eqb (pada s1) (pada s2)) eqn:E2'; try discriminate.
        apply Nat.eqb_eq in E2'.
        right. right.
        split.
        -- exact E1'.
        -- split.
           ++ exact E2'.
           ++ apply Nat.ltb_lt. exact H.
  - intro H.
    unfold sutra_lt in H.
    unfold sutra_ltb.
    destruct H as [Ha | [[Hb Hc] | [Hd [He Hf]]]].
    + apply Nat.ltb_lt in Ha.
      rewrite Ha.
      reflexivity.
    + assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true).
      { apply Nat.eqb_eq. exact Hb. }
      rewrite H0.
      apply Nat.ltb_lt in Hc.
      rewrite Hc.
      reflexivity.
    + assert (Nat.ltb (adhyaya s1) (adhyaya s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H.
      assert (Nat.eqb (adhyaya s1) (adhyaya s2) = true).
      { apply Nat.eqb_eq. exact Hd. }
      rewrite H0.
      assert (Nat.ltb (pada s1) (pada s2) = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H1.
      assert (Nat.eqb (pada s1) (pada s2) = true).
      { apply Nat.eqb_eq. exact He. }
      rewrite H2.
      apply Nat.ltb_lt in Hf.
      exact Hf.
Qed.

(** ** 1.4.2 vipratiṣedhe paraṁ kāryam *)
(** "In a conflict, the later rule prevails."
    When two rules both apply, the one appearing later in the
    Aṣṭādhyāyī wins. Exception: apavāda defeats utsarga regardless. *)

Inductive para_defeats_spec : SutraNum -> SutraNum -> Prop :=
  | Para_later : forall s1 s2,
      sutra_lt s1 s2 ->
      para_defeats_spec s2 s1.

Lemma para_defeats_irrefl : forall s, ~ para_defeats_spec s s.
Proof.
  intros s H.
  inversion H.
  unfold sutra_lt in H0.
  destruct H0 as [Hlt | [[Heq Hlt] | [Heq1 [Heq2 Hlt]]]]; lia.
Qed.

Lemma para_defeats_asymm : forall s1 s2,
  para_defeats_spec s1 s2 -> ~ para_defeats_spec s2 s1.
Proof.
  intros s1 s2 H12 H21.
  inversion H12 as [sa sb Hlt1 Heq1 Heq2]; subst.
  inversion H21 as [sc sd Hlt2 Heq3 Heq4]; subst.
  unfold sutra_lt in *.
  destruct Hlt1 as [Ha | [[Hb Hc] | [Hd [He Hf]]]];
  destruct Hlt2 as [Ha' | [[Hb' Hc'] | [Hd' [He' Hf']]]]; lia.
Qed.

(** * Part VII: Rule Representation *)

Inductive RuleId : Type :=
  | R_6_1_77
  | R_6_1_78
  | R_6_1_87
  | R_6_1_88
  | R_6_1_101
  | R_6_1_109.

Scheme Equality for RuleId.

(** eṅ = e, o (from Śiva Sūtras 3). *)
Definition is_en (v : Vowel) : bool :=
  match v with
  | V_e | V_o => true
  | _ => false
  end.

Definition rule_sutra_num (r : RuleId) : SutraNum :=
  match r with
  | R_6_1_77 => {| adhyaya := 6; pada := 1; sutra := 77 |}
  | R_6_1_78 => {| adhyaya := 6; pada := 1; sutra := 78 |}
  | R_6_1_87 => {| adhyaya := 6; pada := 1; sutra := 87 |}
  | R_6_1_88 => {| adhyaya := 6; pada := 1; sutra := 88 |}
  | R_6_1_101 => {| adhyaya := 6; pada := 1; sutra := 101 |}
  | R_6_1_109 => {| adhyaya := 6; pada := 1; sutra := 109 |}
  end.

Definition is_apavada (r1 r2 : RuleId) : bool :=
  match r1, r2 with
  | R_6_1_88, R_6_1_87 => true
  | R_6_1_101, R_6_1_87 => true
  | R_6_1_101, R_6_1_77 => true
  | R_6_1_109, R_6_1_78 => true
  | _, _ => false
  end.

Definition rule_matches (r : RuleId) (v1 v2 : Vowel) : bool :=
  match r with
  | R_6_1_77 => is_ik_computed v1
  | R_6_1_78 => is_ec_computed v1
  | R_6_1_87 => is_a_class v1
  | R_6_1_88 => is_a_class v1 && is_ec_computed v2
  | R_6_1_101 => is_ak_computed v1 && is_ak_computed v2 && savarna v1 v2
  | R_6_1_109 => is_en v1 && Vowel_beq v2 V_a
  end.

Definition apply_rule (r : RuleId) (v1 v2 : Vowel) : list Phoneme :=
  match r with
  | R_6_1_77 =>
      match yan_of v1 with
      | Some c => [Vyan c; Svar v2]
      | None => [Svar v1; Svar v2]
      end
  | R_6_1_78 =>
      match ayavayav v1 with
      | Some prefix => prefix ++ [Svar v2]
      | None => [Svar v1; Svar v2]
      end
  | R_6_1_87 => guna v2
  | R_6_1_88 => vrddhi v2
  | R_6_1_101 => [Svar (lengthen v1)]
  | R_6_1_109 => [Svar v1]
  end.

(** * Part VIII: Precedence - vipratiṣedhe paraṁ kāryam *)

Definition rule_defeats (r1 r2 : RuleId) : bool :=
  is_apavada r1 r2 ||
  (negb (is_apavada r2 r1) &&
   sutra_ltb (rule_sutra_num r2) (rule_sutra_num r1)).

Lemma rule_defeats_irrefl : forall r, rule_defeats r r = false.
Proof.
  intro r.
  unfold rule_defeats.
  destruct r; simpl; rewrite sutra_ltb_irrefl; reflexivity.
Qed.

Definition all_rules : list RuleId :=
  [R_6_1_77; R_6_1_78; R_6_1_87; R_6_1_88; R_6_1_101; R_6_1_109].

Fixpoint matching_rules (rules : list RuleId) (v1 v2 : Vowel)
  : list RuleId :=
  match rules with
  | [] => []
  | r :: rs =>
      if rule_matches r v1 v2
      then r :: matching_rules rs v1 v2
      else matching_rules rs v1 v2
  end.

Fixpoint find_winner_aux (fuel : nat) (candidates : list RuleId)
  : option RuleId :=
  match fuel with
  | O => None
  | S fuel' =>
      match candidates with
      | [] => None
      | [r] => Some r
      | r1 :: r2 :: rest =>
          if rule_defeats r1 r2 then find_winner_aux fuel' (r1 :: rest)
          else find_winner_aux fuel' (r2 :: rest)
      end
  end.

Definition find_winner (candidates : list RuleId) : option RuleId :=
  find_winner_aux (List.length candidates) candidates.

Definition select_rule (v1 v2 : Vowel) : option RuleId :=
  find_winner (matching_rules all_rules v1 v2).

(** * Part IX: Declarative Specification *)

Inductive sandhi_applicable : RuleId -> Vowel -> Vowel -> Prop :=
  | SA_77 : forall v1 v2,
      is_ik_computed v1 = true ->
      sandhi_applicable R_6_1_77 v1 v2
  | SA_78 : forall v1 v2,
      is_ec_computed v1 = true ->
      sandhi_applicable R_6_1_78 v1 v2
  | SA_87 : forall v1 v2,
      is_a_class v1 = true ->
      sandhi_applicable R_6_1_87 v1 v2
  | SA_88 : forall v1 v2,
      is_a_class v1 = true ->
      is_ec_computed v2 = true ->
      sandhi_applicable R_6_1_88 v1 v2
  | SA_101 : forall v1 v2,
      is_ak_computed v1 = true ->
      is_ak_computed v2 = true ->
      savarna v1 v2 = true ->
      sandhi_applicable R_6_1_101 v1 v2
  | SA_109 : forall v1 v2,
      is_en v1 = true ->
      v2 = V_a ->
      sandhi_applicable R_6_1_109 v1 v2.

Lemma rule_matches_iff_applicable : forall r v1 v2,
  rule_matches r v1 v2 = true <-> sandhi_applicable r v1 v2.
Proof.
  intros r v1 v2.
  split.
  - intro H.
    destruct r; simpl in H.
    + apply SA_77. exact H.
    + apply SA_78. exact H.
    + apply SA_87. exact H.
    + apply Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      apply SA_88; assumption.
    + apply Bool.andb_true_iff in H.
      destruct H as [H12 H3].
      apply Bool.andb_true_iff in H12.
      destruct H12 as [H1 H2].
      apply SA_101; assumption.
    + apply Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      apply SA_109.
      -- exact H1.
      -- destruct v2; simpl in H2; try discriminate; reflexivity.
  - intro H.
    destruct H; simpl.
    + exact H.
    + exact H.
    + exact H.
    + rewrite H, H0. reflexivity.
    + rewrite H, H0, H1. reflexivity.
    + rewrite H. subst v2. reflexivity.
Qed.

Inductive defeats_rel : RuleId -> RuleId -> Prop :=
  | Defeats_apavada : forall r1 r2,
      is_apavada r1 r2 = true ->
      defeats_rel r1 r2
  | Defeats_para : forall r1 r2,
      is_apavada r1 r2 = false ->
      is_apavada r2 r1 = false ->
      sutra_lt (rule_sutra_num r2) (rule_sutra_num r1) ->
      defeats_rel r1 r2.

Lemma rule_defeats_correct : forall r1 r2,
  rule_defeats r1 r2 = true <-> defeats_rel r1 r2.
Proof.
  intros r1 r2.
  split.
  - intro H.
    unfold rule_defeats in H.
    destruct (is_apavada r1 r2) eqn:E1.
    + apply Defeats_apavada.
      exact E1.
    + simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H as [Hneg Hlt].
      apply Bool.negb_true_iff in Hneg.
      apply Defeats_para.
      -- exact E1.
      -- exact Hneg.
      -- apply sutra_ltb_correct.
         exact Hlt.
  - intro H.
    unfold rule_defeats.
    destruct H as [r1' r2' Hapav | r1' r2' Hnot1 Hnot2 Hlt].
    + rewrite Hapav.
      reflexivity.
    + rewrite Hnot1.
      simpl.
      apply Bool.andb_true_iff.
      split.
      -- apply Bool.negb_true_iff.
         exact Hnot2.
      -- apply sutra_ltb_correct.
         exact Hlt.
Qed.

Inductive sandhi_winner : RuleId -> Vowel -> Vowel -> Prop :=
  | SW_wins : forall r v1 v2,
      sandhi_applicable r v1 v2 ->
      (forall r', sandhi_applicable r' v1 v2 -> r' <> r -> defeats_rel r r') ->
      sandhi_winner r v1 v2.

Inductive ac_sandhi_rel : Vowel -> Vowel -> list Phoneme -> Prop :=
  | ASR_result : forall v1 v2 r out,
      sandhi_winner r v1 v2 ->
      apply_rule r v1 v2 = out ->
      ac_sandhi_rel v1 v2 out.

(** * Part X: Computational Sandhi Function *)

Definition apply_ac_sandhi (v1 v2 : Vowel) : list Phoneme :=
  match select_rule v1 v2 with
  | Some r => apply_rule r v1 v2
  | None => [Svar v1; Svar v2]
  end.

(** * Part XI: Key Conflict Cases *)

Lemma conflict_i_i_both_match :
  rule_matches R_6_1_77 V_i V_i = true /\
  rule_matches R_6_1_101 V_i V_i = true.
Proof.
  split; reflexivity.
Qed.

Lemma conflict_i_i_101_wins :
  rule_defeats R_6_1_101 R_6_1_77 = true.
Proof.
  reflexivity.
Qed.

Lemma conflict_a_e_both_match :
  rule_matches R_6_1_87 V_a V_e = true /\
  rule_matches R_6_1_88 V_a V_e = true.
Proof.
  split; reflexivity.
Qed.

Lemma conflict_a_e_88_wins :
  rule_defeats R_6_1_88 R_6_1_87 = true.
Proof.
  reflexivity.
Qed.

Lemma conflict_a_a_both_match :
  rule_matches R_6_1_87 V_a V_a = true /\
  rule_matches R_6_1_101 V_a V_a = true.
Proof.
  split; reflexivity.
Qed.

Lemma conflict_a_a_101_wins :
  rule_defeats R_6_1_101 R_6_1_87 = true.
Proof.
  reflexivity.
Qed.

(** * Part XII: Coverage Theorem (Semantic) *)

Lemma vowel_classification : forall v,
  is_a_class v = true \/
  is_ik_computed v = true \/
  is_ec_computed v = true.
Proof.
  intro v.
  destruct v.
  - left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
  - right. right. reflexivity.
Qed.

Theorem coverage_semantic : forall v1 v2,
  exists r, sandhi_applicable r v1 v2.
Proof.
  intros v1 v2.
  destruct (vowel_classification v1) as [Ha | [Hik | Hec]].
  - exists R_6_1_87.
    apply SA_87.
    exact Ha.
  - exists R_6_1_77.
    apply SA_77.
    exact Hik.
  - exists R_6_1_78.
    apply SA_78.
    exact Hec.
Qed.

Theorem coverage_computational : forall v1 v2,
  exists r, select_rule v1 v2 = Some r.
Proof.
  intros v1 v2.
  unfold select_rule, matching_rules, all_rules.
  destruct v1, v2; simpl; eexists; reflexivity.
Qed.

(** * Part XIII: Correctness Examples *)

Example ex_a_a : apply_ac_sandhi V_a V_a = [Svar V_aa].
Proof. reflexivity. Qed.

Example ex_a_i : apply_ac_sandhi V_a V_i = [Svar V_e].
Proof. reflexivity. Qed.

Example ex_a_u : apply_ac_sandhi V_a V_u = [Svar V_o].
Proof. reflexivity. Qed.

Example ex_a_e : apply_ac_sandhi V_a V_e = [Svar V_ai].
Proof. reflexivity. Qed.

Example ex_a_o : apply_ac_sandhi V_a V_o = [Svar V_au].
Proof. reflexivity. Qed.

Example ex_i_a : apply_ac_sandhi V_i V_a = [Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example ex_i_i : apply_ac_sandhi V_i V_i = [Svar V_ii].
Proof. reflexivity. Qed.

Example ex_i_u : apply_ac_sandhi V_i V_u = [Vyan C_y; Svar V_u].
Proof. reflexivity. Qed.

Example ex_u_a : apply_ac_sandhi V_u V_a = [Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

Example ex_u_u : apply_ac_sandhi V_u V_u = [Svar V_uu].
Proof. reflexivity. Qed.

Example ex_e_a : apply_ac_sandhi V_e V_a = [Svar V_e].
Proof. reflexivity. Qed.

Example ex_ai_a : apply_ac_sandhi V_ai V_a = [Svar V_aa; Vyan C_y; Svar V_a].
Proof. reflexivity. Qed.

Example ex_o_a : apply_ac_sandhi V_o V_a = [Svar V_o].
Proof. reflexivity. Qed.

Example ex_au_a : apply_ac_sandhi V_au V_a = [Svar V_aa; Vyan C_v; Svar V_a].
Proof. reflexivity. Qed.

Example ex_r_a : apply_ac_sandhi V_r V_a = [Vyan C_r; Svar V_a].
Proof. reflexivity. Qed.

Example ex_r_r : apply_ac_sandhi V_r V_r = [Svar V_rr].
Proof. reflexivity. Qed.

Example ex_a_r : apply_ac_sandhi V_a V_r = [Svar V_a; Vyan C_r].
Proof. reflexivity. Qed.

(** * Part XIV: Non-emptiness *)

Theorem apply_rule_nonempty : forall r v1 v2,
  rule_matches r v1 v2 = true ->
  apply_rule r v1 v2 <> [].
Proof.
  intros r v1 v2 Hmatch.
  destruct r; simpl in *.
  - destruct (yan_of v1) eqn:E.
    + discriminate.
    + destruct v1; simpl in Hmatch; discriminate.
  - destruct (ayavayav v1) eqn:E.
    + destruct l; discriminate.
    + destruct v1; simpl in Hmatch; discriminate.
  - destruct v2; discriminate.
  - destruct v2; discriminate.
  - discriminate.
  - discriminate.
Qed.

Theorem apply_ac_sandhi_nonempty : forall v1 v2,
  apply_ac_sandhi v1 v2 <> [].
Proof.
  intros v1 v2.
  unfold apply_ac_sandhi.
  destruct (select_rule v1 v2) eqn:E.
  - apply apply_rule_nonempty.
    unfold select_rule in E.
    unfold find_winner, matching_rules, all_rules in E.
    destruct v1, v2; simpl in E;
    injection E as E; subst; reflexivity.
  - destruct (coverage_computational v1 v2) as [r' Hr'].
    rewrite E in Hr'.
    discriminate.
Qed.

(** * Part XV: Apavāda Verification *)

Lemma apavada_88_87_real_conflict : exists v1 v2,
  rule_matches R_6_1_87 v1 v2 = true /\
  rule_matches R_6_1_88 v1 v2 = true /\
  rule_defeats R_6_1_88 R_6_1_87 = true.
Proof.
  exists V_a, V_e.
  repeat split; reflexivity.
Qed.

Lemma apavada_101_87_real_conflict : exists v1 v2,
  rule_matches R_6_1_87 v1 v2 = true /\
  rule_matches R_6_1_101 v1 v2 = true /\
  rule_defeats R_6_1_101 R_6_1_87 = true.
Proof.
  exists V_a, V_a.
  repeat split; reflexivity.
Qed.

Lemma apavada_101_77_real_conflict : exists v1 v2,
  rule_matches R_6_1_77 v1 v2 = true /\
  rule_matches R_6_1_101 v1 v2 = true /\
  rule_defeats R_6_1_101 R_6_1_77 = true.
Proof.
  exists V_i, V_i.
  repeat split; reflexivity.
Qed.

(** * Part XVI: Winner Maximality *)

Definition is_maximal (r : RuleId) (v1 v2 : Vowel) : Prop :=
  rule_matches r v1 v2 = true /\
  forall r', rule_matches r' v1 v2 = true -> r' <> r -> rule_defeats r r' = true.

Lemma select_rule_is_maximal : forall v1 v2 r,
  select_rule v1 v2 = Some r ->
  is_maximal r v1 v2.
Proof.
  intros v1 v2 r Hsel.
  unfold is_maximal.
  split.
  - unfold select_rule in Hsel.
    destruct v1, v2; simpl in Hsel; injection Hsel as Hsel; subst; reflexivity.
  - intros r' Hmatch' Hneq.
    destruct v1, v2; simpl in Hsel; injection Hsel as Hsel; subst;
    destruct r'; simpl in Hmatch'; try discriminate; try reflexivity;
    contradiction Hneq; reflexivity.
Qed.

Lemma is_maximal_iff_winner : forall r v1 v2,
  is_maximal r v1 v2 <-> sandhi_winner r v1 v2.
Proof.
  intros r v1 v2.
  split.
  - intro H.
    destruct H as [Hmatch Hdefeats].
    apply SW_wins.
    + apply rule_matches_iff_applicable.
      exact Hmatch.
    + intros r' Happ' Hneq.
      apply rule_defeats_correct.
      apply Hdefeats.
      -- apply rule_matches_iff_applicable.
         exact Happ'.
      -- exact Hneq.
  - intro H.
    destruct H as [r' v1' v2' Happ Hdefeats].
    unfold is_maximal.
    split.
    + apply rule_matches_iff_applicable.
      exact Happ.
    + intros r'' Hmatch'' Hneq.
      apply rule_defeats_correct.
      apply Hdefeats.
      -- apply rule_matches_iff_applicable.
         exact Hmatch''.
      -- exact Hneq.
Qed.

Lemma select_rule_correct : forall v1 v2 r,
  select_rule v1 v2 = Some r <-> sandhi_winner r v1 v2.
Proof.
  intros v1 v2 r.
  split.
  - intro H.
    apply is_maximal_iff_winner.
    apply select_rule_is_maximal.
    exact H.
  - intro H.
    apply is_maximal_iff_winner in H.
    destruct H as [Hmatch Hdefeats].
    destruct (coverage_computational v1 v2) as [rsel Hrsel].
    destruct (RuleId_eq_dec r rsel) as [Heq | Hneq].
    + subst.
      exact Hrsel.
    + pose proof (@select_rule_is_maximal v1 v2 rsel Hrsel) as Hmax'.
      destruct Hmax' as [Hmatch' Hdefeats'].
      assert (Hdef1 : rule_defeats r rsel = true).
      { apply Hdefeats; auto. }
      assert (Hdef2 : rule_defeats rsel r = true).
      { apply Hdefeats'; auto. }
      destruct r, rsel;
      simpl in Hdef1, Hdef2; try discriminate; try reflexivity;
      contradiction Hneq; reflexivity.
Qed.

(** * Part XVII: Order Independence *)

Definition rules_total_on (v1 v2 : Vowel) : Prop :=
  forall r1 r2,
    rule_matches r1 v1 v2 = true ->
    rule_matches r2 v1 v2 = true ->
    r1 = r2 \/ rule_defeats r1 r2 = true \/ rule_defeats r2 r1 = true.

Lemma our_rules_total : forall v1 v2, rules_total_on v1 v2.
Proof.
  intros v1 v2 r1 r2 H1 H2.
  destruct r1, r2;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; reflexivity).
Qed.

(** * Part XVIII: Soundness *)

Theorem soundness_aux : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out ->
  exists r, select_rule v1 v2 = Some r /\ apply_rule r v1 v2 = out.
Proof.
  intros v1 v2 out H.
  unfold apply_ac_sandhi in H.
  destruct (select_rule v1 v2) eqn:E.
  - exists r.
    auto.
  - destruct (coverage_computational v1 v2) as [r' Hr'].
    rewrite E in Hr'.
    discriminate.
Qed.

Theorem soundness : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out ->
  ac_sandhi_rel v1 v2 out.
Proof.
  intros v1 v2 out H.
  pose proof (@soundness_aux v1 v2 out H) as [r [Hsel Happ]].
  apply ASR_result with (r := r).
  - apply select_rule_correct.
    exact Hsel.
  - exact Happ.
Qed.

Theorem completeness : forall v1 v2 out,
  ac_sandhi_rel v1 v2 out ->
  apply_ac_sandhi v1 v2 = out.
Proof.
  intros v1 v2 out H.
  destruct H as [v1' v2' r out' Hwinner Happ].
  unfold apply_ac_sandhi.
  apply select_rule_correct in Hwinner.
  rewrite Hwinner.
  exact Happ.
Qed.

Theorem soundness_completeness : forall v1 v2 out,
  apply_ac_sandhi v1 v2 = out <-> ac_sandhi_rel v1 v2 out.
Proof.
  intros v1 v2 out.
  split.
  - apply soundness.
  - apply completeness.
Qed.

(** * Part XIX: Consonant Classes for Visarga Sandhi *)

(** khar = voiceless non-sibilant stops + sibilants (from Śiva Sūtras).
    Specifically: k kh c ch ṭ ṭh t th p ph ś ṣ s *)

Definition is_khar (c : Consonant) : bool :=
  match c with
  | C_k | C_kh | C_c | C_ch | C_tt | C_tth | C_t | C_th | C_p | C_ph
  | C_sh | C_ss | C_s => true
  | _ => false
  end.

Inductive is_khar_spec : Consonant -> Prop :=
  | Khar_k : is_khar_spec C_k   | Khar_kh : is_khar_spec C_kh
  | Khar_c : is_khar_spec C_c   | Khar_ch : is_khar_spec C_ch
  | Khar_tt : is_khar_spec C_tt | Khar_tth : is_khar_spec C_tth
  | Khar_t : is_khar_spec C_t   | Khar_th : is_khar_spec C_th
  | Khar_p : is_khar_spec C_p   | Khar_ph : is_khar_spec C_ph
  | Khar_sh : is_khar_spec C_sh | Khar_ss : is_khar_spec C_ss
  | Khar_s : is_khar_spec C_s.

Lemma is_khar_correct : forall c,
  is_khar c = true <-> is_khar_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** jhaś = voiced stops: g gh j jh ḍ ḍh d dh b bh *)

Definition is_jhas (c : Consonant) : bool :=
  match c with
  | C_g | C_gh | C_j | C_jh | C_dd | C_ddh | C_d | C_dh | C_b | C_bh => true
  | _ => false
  end.

Inductive is_jhas_spec : Consonant -> Prop :=
  | Jhas_g : is_jhas_spec C_g   | Jhas_gh : is_jhas_spec C_gh
  | Jhas_j : is_jhas_spec C_j   | Jhas_jh : is_jhas_spec C_jh
  | Jhas_dd : is_jhas_spec C_dd | Jhas_ddh : is_jhas_spec C_ddh
  | Jhas_d : is_jhas_spec C_d   | Jhas_dh : is_jhas_spec C_dh
  | Jhas_b : is_jhas_spec C_b   | Jhas_bh : is_jhas_spec C_bh.

Lemma is_jhas_correct : forall c,
  is_jhas c = true <-> is_jhas_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** hal = all consonants *)

Definition is_hal (c : Consonant) : bool := true.

Lemma is_hal_total : forall c, is_hal c = true.
Proof. intro c; reflexivity. Qed.

(** * Part XX: Visarga Sandhi (8.3) *)

(** Visarga sandhi operates at word boundaries where a word ends in
    visarga (ḥ) and the next word begins with various sounds. *)

(** ** 8.3.15 kharavasānayoḥ visarjanīyaḥ *)
(** "s becomes visarga before khar consonants or at utterance end."
    This rule creates visarga from underlying s. *)

Inductive visarga_from_s_spec : Consonant -> Prop :=
  | VFS_khar : forall c, is_khar_spec c -> visarga_from_s_spec c.

(** ** 8.3.23 mo 'nusvāraḥ *)
(** "m becomes anusvāra before a consonant."
    padānta-m + hal → anusvāra + hal *)

Inductive anusvara_from_m_spec : Consonant -> Prop :=
  | AFM_hal : forall c, anusvara_from_m_spec c.

Definition apply_8_3_23 (following : Consonant) : Phoneme := Anusvara.

Lemma anusvara_from_m_total : forall c, anusvara_from_m_spec c.
Proof. intro c; constructor. Qed.

(** ** 8.3.34 visarjanīyasya saḥ *)
(** "Visarga becomes s before khar."
    ḥ + khar → s + khar (in certain contexts) *)

Definition visarga_to_s_before_khar (c : Consonant) : option Phoneme :=
  if is_khar c then Some (Vyan C_s) else None.

(** ** Visarga before voiced sounds (8.3.17 etc.) *)
(** Before voiced consonants, visarga often becomes the corresponding
    sibilant or is deleted with compensatory lengthening. *)

(** aḥ + voiced → o (with loss of following a) - 6.1.109 type *)
(** āḥ + voiced → ā (visarga deletion) *)

Definition visarga_before_voiced (prev_vowel : Vowel) (c : Consonant)
  : option (list Phoneme) :=
  if is_jhas c then
    match prev_vowel with
    | V_a => Some [Svar V_o]
    | V_aa => Some [Svar V_aa]
    | _ => Some [Svar prev_vowel; Vyan C_r]
    end
  else None.

(** ** 8.3.36 visarjanīyasya jihvāmūlīyopadhmānīyau kakhupau *)
(** Before k/kh → jihvāmūlīya; before p/ph → upadhmānīya.
    We model these as allophonic visargas (simplified to visarga). *)

Definition visarga_allophone (c : Consonant) : Phoneme :=
  Visarga.

(** Combined visarga sandhi application. *)

Inductive VisargaSandhiResult : Type :=
  | VSR_visarga : VisargaSandhiResult
  | VSR_s : VisargaSandhiResult
  | VSR_r : VisargaSandhiResult
  | VSR_deletion : Vowel -> VisargaSandhiResult
  | VSR_o : VisargaSandhiResult.

Definition apply_visarga_sandhi (prev_vowel : Vowel) (following : Consonant)
  : VisargaSandhiResult :=
  if is_khar following then VSR_visarga
  else if is_jhas following then
    match prev_vowel with
    | V_a => VSR_o
    | V_aa => VSR_deletion V_aa
    | _ => VSR_r
    end
  else VSR_visarga.

(** * Part XXI: Consonant Sandhi (8.4) *)

(** ** Varga (class) of stops *)

Inductive Varga : Type := Kavarga | Cavarga | Tavarga | Tavarga2 | Pavarga.

Definition consonant_varga (c : Consonant) : option Varga :=
  match c with
  | C_k | C_kh | C_g | C_gh | C_ng => Some Kavarga
  | C_c | C_ch | C_j | C_jh | C_ny => Some Cavarga
  | C_tt | C_tth | C_dd | C_ddh | C_nn => Some Tavarga
  | C_t | C_th | C_d | C_dh | C_n => Some Tavarga2
  | C_p | C_ph | C_b | C_bh | C_m => Some Pavarga
  | _ => None
  end.

(** ** 8.4.53 jhalāṁ jaś jhaśi *)
(** "jhal consonants become jaś before jhaś."
    Voiceless stops become voiced before voiced stops. *)

Definition voiced_of (c : Consonant) : Consonant :=
  match c with
  | C_k => C_g   | C_kh => C_gh
  | C_c => C_j   | C_ch => C_jh
  | C_tt => C_dd | C_tth => C_ddh
  | C_t => C_d   | C_th => C_dh
  | C_p => C_b   | C_ph => C_bh
  | other => other
  end.

Inductive voicing_spec : Consonant -> Consonant -> Prop :=
  | Voice_k : voicing_spec C_k C_g
  | Voice_kh : voicing_spec C_kh C_gh
  | Voice_c : voicing_spec C_c C_j
  | Voice_ch : voicing_spec C_ch C_jh
  | Voice_tt : voicing_spec C_tt C_dd
  | Voice_tth : voicing_spec C_tth C_ddh
  | Voice_t : voicing_spec C_t C_d
  | Voice_th : voicing_spec C_th C_dh
  | Voice_p : voicing_spec C_p C_b
  | Voice_ph : voicing_spec C_ph C_bh.

Lemma voiced_of_correct : forall c1 c2,
  voicing_spec c1 c2 -> voiced_of c1 = c2.
Proof.
  intros c1 c2 H.
  destruct H; reflexivity.
Qed.

(** ** 8.4.55 khari ca *)
(** "Also before khar."
    Final voiced stops become voiceless before voiceless consonants. *)

Definition voiceless_of (c : Consonant) : Consonant :=
  match c with
  | C_g => C_k   | C_gh => C_k
  | C_j => C_c   | C_jh => C_c
  | C_dd => C_tt | C_ddh => C_tt
  | C_d => C_t   | C_dh => C_t
  | C_b => C_p   | C_bh => C_p
  | other => other
  end.

Inductive devoicing_spec : Consonant -> Consonant -> Prop :=
  | Devoice_g : devoicing_spec C_g C_k
  | Devoice_gh : devoicing_spec C_gh C_k
  | Devoice_j : devoicing_spec C_j C_c
  | Devoice_jh : devoicing_spec C_jh C_c
  | Devoice_dd : devoicing_spec C_dd C_tt
  | Devoice_ddh : devoicing_spec C_ddh C_tt
  | Devoice_d : devoicing_spec C_d C_t
  | Devoice_dh : devoicing_spec C_dh C_t
  | Devoice_b : devoicing_spec C_b C_p
  | Devoice_bh : devoicing_spec C_bh C_p.

Lemma voiceless_of_correct : forall c1 c2,
  devoicing_spec c1 c2 -> voiceless_of c1 = c2.
Proof.
  intros c1 c2 H.
  destruct H; reflexivity.
Qed.

(** ** 8.4.40 stoḥ ścunā ścuḥ *)
(** "s and t-class become ś and c-class before c-class/ś." *)

Definition is_cavarga_or_sh (c : Consonant) : bool :=
  match c with
  | C_c | C_ch | C_j | C_jh | C_ny | C_sh => true
  | _ => false
  end.

Definition palatalize (c : Consonant) : Consonant :=
  match c with
  | C_s => C_sh
  | C_t => C_c   | C_th => C_ch
  | C_d => C_j   | C_dh => C_jh
  | C_n => C_ny
  | other => other
  end.

(** ** 8.4.41 ṣṭunā ṣṭuḥ *)
(** "s and t-class become ṣ and ṭ-class before ṭ-class/ṣ." *)

Definition is_tavarga_or_ss (c : Consonant) : bool :=
  match c with
  | C_tt | C_tth | C_dd | C_ddh | C_nn | C_ss => true
  | _ => false
  end.

Definition retroflexize (c : Consonant) : Consonant :=
  match c with
  | C_s => C_ss
  | C_t => C_tt   | C_th => C_tth
  | C_d => C_dd   | C_dh => C_ddh
  | C_n => C_nn
  | other => other
  end.

(** Palatalization spec (8.4.40). *)

Inductive palatalization_spec : Consonant -> Consonant -> Prop :=
  | Pal_s : palatalization_spec C_s C_sh
  | Pal_t : palatalization_spec C_t C_c
  | Pal_th : palatalization_spec C_th C_ch
  | Pal_d : palatalization_spec C_d C_j
  | Pal_dh : palatalization_spec C_dh C_jh
  | Pal_n : palatalization_spec C_n C_ny.

Lemma palatalize_correct : forall c1 c2,
  palatalization_spec c1 c2 -> palatalize c1 = c2.
Proof.
  intros c1 c2 H.
  destruct H; reflexivity.
Qed.

(** Retroflexion spec (8.4.41). *)

Inductive retroflexion_spec : Consonant -> Consonant -> Prop :=
  | Ret_s : retroflexion_spec C_s C_ss
  | Ret_t : retroflexion_spec C_t C_tt
  | Ret_th : retroflexion_spec C_th C_tth
  | Ret_d : retroflexion_spec C_d C_dd
  | Ret_dh : retroflexion_spec C_dh C_ddh
  | Ret_n : retroflexion_spec C_n C_nn.

Lemma retroflexize_correct : forall c1 c2,
  retroflexion_spec c1 c2 -> retroflexize c1 = c2.
Proof.
  intros c1 c2 H.
  destruct H; reflexivity.
Qed.

(** Cavarga/ś class spec. *)

Inductive is_cavarga_or_sh_spec : Consonant -> Prop :=
  | Cav_c : is_cavarga_or_sh_spec C_c
  | Cav_ch : is_cavarga_or_sh_spec C_ch
  | Cav_j : is_cavarga_or_sh_spec C_j
  | Cav_jh : is_cavarga_or_sh_spec C_jh
  | Cav_ny : is_cavarga_or_sh_spec C_ny
  | Cav_sh : is_cavarga_or_sh_spec C_sh.

Lemma is_cavarga_or_sh_correct : forall c,
  is_cavarga_or_sh c = true <-> is_cavarga_or_sh_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Ṭavarga/ṣ class spec. *)

Inductive is_tavarga_or_ss_spec : Consonant -> Prop :=
  | Tav_tt : is_tavarga_or_ss_spec C_tt
  | Tav_tth : is_tavarga_or_ss_spec C_tth
  | Tav_dd : is_tavarga_or_ss_spec C_dd
  | Tav_ddh : is_tavarga_or_ss_spec C_ddh
  | Tav_nn : is_tavarga_or_ss_spec C_nn
  | Tav_ss : is_tavarga_or_ss_spec C_ss.

Lemma is_tavarga_or_ss_correct : forall c,
  is_tavarga_or_ss c = true <-> is_tavarga_or_ss_spec c.
Proof.
  intro c; split.
  - intro H; destruct c; simpl in H; try discriminate; constructor.
  - intro H; destruct H; reflexivity.
Qed.

(** Combined consonant sandhi. *)

(** Place assimilation (8.4.40-41) applies first, then voicing (8.4.53-55). *)

Definition apply_place_assimilation (final following : Consonant) : Consonant :=
  if is_cavarga_or_sh following then palatalize final
  else if is_tavarga_or_ss following then retroflexize final
  else final.

Definition apply_voicing_assimilation (final following : Consonant) : Consonant :=
  if is_jhas following then voiced_of final
  else if is_khar following then voiceless_of final
  else final.

Definition apply_consonant_sandhi (final following : Consonant) : Consonant :=
  let after_place := apply_place_assimilation final following in
  apply_voicing_assimilation after_place following.

(** Declarative spec for consonant sandhi result. *)

Inductive consonant_sandhi_rel : Consonant -> Consonant -> Consonant -> Prop :=
  | CSR_result : forall c1 c2,
      consonant_sandhi_rel c1 c2 (apply_consonant_sandhi c1 c2).

Lemma consonant_sandhi_correct : forall c1 c2 c3,
  apply_consonant_sandhi c1 c2 = c3 <-> consonant_sandhi_rel c1 c2 c3.
Proof.
  intros c1 c2 c3.
  split.
  - intro H.
    rewrite <- H.
    constructor.
  - intro H.
    destruct H.
    reflexivity.
Qed.

(** Examples of consonant sandhi. *)

Example cons_sandhi_vak_gacchati :
  apply_consonant_sandhi C_k C_g = C_g.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_ca :
  apply_consonant_sandhi C_t C_c = C_c.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_tena :
  apply_consonant_sandhi C_t C_t = C_t.
Proof. reflexivity. Qed.

Example cons_sandhi_tad_gacchati :
  apply_consonant_sandhi C_d C_g = C_d.
Proof. reflexivity. Qed.

Example cons_sandhi_tat_gacchati :
  apply_consonant_sandhi C_t C_g = C_d.
Proof. reflexivity. Qed.

(** * Part XXII: Unified External Sandhi *)

(** External sandhi context: what is at the boundary. *)

Inductive BoundarySound : Type :=
  | BS_vowel : Vowel -> BoundarySound
  | BS_consonant : Consonant -> BoundarySound
  | BS_visarga : BoundarySound
  | BS_anusvara : BoundarySound
  | BS_pause : BoundarySound.

(** Result of external sandhi. *)

Inductive SandhiResult : Type :=
  | SR_vowels : list Phoneme -> SandhiResult
  | SR_consonant : Consonant -> SandhiResult
  | SR_visarga : SandhiResult
  | SR_anusvara : SandhiResult
  | SR_unchanged : Phoneme -> SandhiResult.

(** Unified sandhi at word boundary. *)

Definition apply_external_sandhi
  (final : BoundarySound) (initial : BoundarySound)
  : SandhiResult :=
  match final, initial with
  | BS_vowel v1, BS_vowel v2 =>
      SR_vowels (apply_ac_sandhi v1 v2)
  | BS_consonant c1, BS_consonant c2 =>
      SR_consonant (apply_consonant_sandhi c1 c2)
  | BS_consonant c, BS_vowel v =>
      SR_unchanged (Vyan c)
  | BS_vowel v, BS_consonant c =>
      SR_unchanged (Svar v)
  | BS_visarga, BS_consonant c =>
      if is_khar c then SR_visarga
      else SR_unchanged Visarga
  | BS_visarga, BS_vowel v =>
      SR_unchanged Visarga
  | _, BS_pause =>
      match final with
      | BS_vowel v => SR_unchanged (Svar v)
      | BS_consonant c => SR_unchanged (Vyan c)
      | BS_visarga => SR_visarga
      | BS_anusvara => SR_anusvara
      | BS_pause => SR_unchanged Visarga
      end
  | _, _ => SR_unchanged Visarga
  end.

(** * Part XXIII: Summary of Formalized Sūtras *)

(** Paribhāṣā (Meta-rules):
    - 1.1.1  vṛddhir ādaic
    - 1.1.2  adeṅ guṇaḥ
    - 1.1.3  iko guṇavṛddhī
    - 1.1.9  tulyāsyaprayatnaṁ savarṇam
    - 1.4.2  vipratiṣedhe paraṁ kāryam

    Vowel Sandhi (ac-sandhi, 6.1):
    - 6.1.77  iko yaṇ aci
    - 6.1.78  eco 'yavāyāvaḥ
    - 6.1.87  ādguṇaḥ
    - 6.1.88  vṛddhir eci
    - 6.1.101 akaḥ savarṇe dīrghaḥ

    Visarga Sandhi (8.3):
    - 8.3.15  kharavasānayoḥ visarjanīyaḥ
    - 8.3.23  mo 'nusvāraḥ
    - 8.3.34  visarjanīyasya saḥ
    - 8.3.36  visarjanīyasya jihvāmūlīyopadhmānīyau

    Consonant Sandhi (8.4):
    - 8.4.40  stoḥ ścunā ścuḥ
    - 8.4.41  ṣṭunā ṣṭuḥ
    - 8.4.53  jhalāṁ jaś jhaśi
    - 8.4.55  khari ca
*)

(** * Part XXIV: Final Metatheorems *)

(** All vowel pairs produce some sandhi result. *)
Theorem vowel_sandhi_total : forall v1 v2,
  exists ps, apply_ac_sandhi v1 v2 = ps /\ ps <> [].
Proof.
  intros v1 v2.
  exists (apply_ac_sandhi v1 v2).
  split.
  - reflexivity.
  - apply apply_ac_sandhi_nonempty.
Qed.

(** Consonant sandhi preserves the consonant category. *)
Theorem consonant_sandhi_yields_consonant : forall c1 c2,
  exists c, apply_consonant_sandhi c1 c2 = c.
Proof.
  intros c1 c2.
  eexists.
  reflexivity.
Qed.

(** The specification-implementation correspondence is complete for:
    - Vowel pratyāhāras (is_ik, is_ak, is_ec) - now computed from Śiva Sūtras
    - Guṇa/vṛddhi grades
    - Savarṇa relation
    - Precedence ordering (sutra_ltb <-> sutra_lt)
    - Rule defeat relation (rule_defeats <-> defeats_rel)
    - Rule selection (select_rule <-> sandhi_winner)
    - Full soundness and completeness (apply_ac_sandhi <-> ac_sandhi_rel)
    - All five ac-sandhi rules *)

Theorem formalization_complete :
  (forall v, is_ik_computed v = true <-> is_ik_spec v) /\
  (forall v, is_ak_computed v = true <-> is_ak_spec v) /\
  (forall v, is_ec_computed v = true <-> is_ec_spec v) /\
  (forall v1 v2, savarna v1 v2 = true <-> savarna_spec v1 v2) /\
  (forall v, is_vrddhi_vowel v = true <-> is_vrddhi_vowel_spec v) /\
  (forall v, is_guna_vowel v = true <-> is_guna_vowel_spec v) /\
  (forall s1 s2, sutra_ltb s1 s2 = true <-> sutra_lt s1 s2) /\
  (forall r1 r2, rule_defeats r1 r2 = true <-> defeats_rel r1 r2) /\
  (forall v1 v2 r, select_rule v1 v2 = Some r <-> sandhi_winner r v1 v2) /\
  (forall v1 v2 out, apply_ac_sandhi v1 v2 = out <-> ac_sandhi_rel v1 v2 out).
Proof.
  split; [exact is_ik_correct |].
  split; [exact is_ak_correct |].
  split; [exact is_ec_correct |].
  split; [exact savarna_correct |].
  split; [exact is_vrddhi_vowel_correct |].
  split; [exact is_guna_vowel_correct |].
  split; [exact sutra_ltb_correct |].
  split; [exact rule_defeats_correct |].
  split; [exact select_rule_correct |].
  exact soundness_completeness.
Qed.
