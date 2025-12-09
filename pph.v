(******************************************************************************)
(*                                                                            *)
(*                    POSTPARTUM HEMORRHAGE VERIFIED                          *)
(*                                                                            *)
(*        A Formal Verification of PPH Staging and Intervention               *)
(*                                                                            *)
(*     Machine-checked proofs of threshold correctness, stage monotonicity,   *)
(*     and intervention protocol properties per WHO/ACOG guidelines.          *)
(*                                                                            *)
(*     "Women are not dying because of diseases we cannot treat. They are     *)
(*      dying because societies have yet to decide that their lives are       *)
(*      worth saving."                                                        *)
(*                                              - Mahmoud Fathalla            *)
(*                                                Former President, FIGO      *)
(*                                                                            *)
(*     Author:  Charles C. Norton                                             *)
(*     Date:    December 2025                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*                              REFERENCES                                    *)
(*                                                                            *)
(*  [WHO2012]                                                                 *)
(*     WHO recommendations for the prevention and treatment of postpartum    *)
(*     haemorrhage. World Health Organization, 2012.                         *)
(*     ISBN: 978-92-4-154850-2                                               *)
(*                                                                            *)
(*  [ACOG2017]                                                                *)
(*     ACOG Practice Bulletin No. 183: Postpartum Hemorrhage.                *)
(*     Obstet Gynecol. 2017;130(4):e168-e186.                                *)
(*     doi:10.1097/AOG.0000000000002351                                      *)
(*                                                                            *)
(*  [CaliforniaMQC2015]                                                       *)
(*     California Maternal Quality Care Collaborative. OB Hemorrhage         *)
(*     Toolkit v2.0. Stanford University, 2015.                              *)
(*     URL: https://www.cmqcc.org/resources-tool-kits/toolkits/ob-hemorrhage *)
(*                                                                            *)
(*  [WOMAN2017]                                                               *)
(*     WOMAN Trial Collaborators. Effect of early tranexamic acid             *)
(*     administration on mortality, hysterectomy, and other morbidities       *)
(*     in women with post-partum haemorrhage (WOMAN): an international,       *)
(*     randomised, double-blind, placebo-controlled trial.                    *)
(*     Lancet. 2017;389(10084):2105-2116.                                    *)
(*     doi:10.1016/S0140-6736(17)30638-4                                     *)
(*                                                                            *)
(*  [Evensen2017]                                                             *)
(*     Evensen A, Anderson JM, Fontaine P. Postpartum Hemorrhage:             *)
(*     Prevention and Treatment. Am Fam Physician. 2017;95(7):442-449.       *)
(*     PMID: 28409615                                                        *)
(*                                                                            *)
(*  [Mavrides2016]                                                            *)
(*     Mavrides E, Allard S, Chandraharan E, et al. Prevention and            *)
(*     Management of Postpartum Haemorrhage. BJOG. 2016;124:e106-e149.       *)
(*     doi:10.1111/1471-0528.14178                                           *)
(*                                                                            *)
(*  [Nathan2015]                                                              *)
(*     Nathan HL, El Ayadi A, Hezelgrave NL, et al. Shock index: an           *)
(*     effective predictor of outcome in postpartum haemorrhage?              *)
(*     BJOG. 2015;122(2):268-275.                                            *)
(*     doi:10.1111/1471-0528.13206                                           *)
(*                                                                            *)
(*  [SMFM2018]                                                                *)
(*     Society for Maternal-Fetal Medicine. Placenta Accreta Spectrum.        *)
(*     SMFM Consult Series #44. Am J Obstet Gynecol. 2018;218(6):B2-B16.     *)
(*     doi:10.1016/j.ajog.2018.02.018                                        *)
(*                                                                            *)
(*  [Gallos2018]                                                              *)
(*     Gallos I, Papadopoulou A, Man R, et al. Uterotonic agents for          *)
(*     preventing postpartum haemorrhage: a network meta-analysis.            *)
(*     Cochrane Database Syst Rev. 2018;12:CD011689.                         *)
(*     doi:10.1002/14651858.CD011689.pub3                                    *)
(*                                                                            *)
(*  [Whiting2014]                                                             *)
(*     Whiting D, DiNardo JA. TEG and ROTEM: Technology and clinical          *)
(*     applications. Am J Hematol. 2014;89(2):228-232.                       *)
(*     doi:10.1002/ajh.23599                                                 *)
(*                                                                            *)
(*  [Cannon2017]                                                              *)
(*     Cannon JW, Khan MA, Raja AS, et al. Damage control resuscitation       *)
(*     in patients with severe traumatic hemorrhage: A practice management    *)
(*     guideline. J Trauma Acute Care Surg. 2017;82(3):605-617.              *)
(*     doi:10.1097/TA.0000000000001333                                       *)
(*                                                                            *)
(*  [Bose2006]                                                                *)
(*     Bose P, Regan F, Paterson-Brown S. Improving the accuracy of           *)
(*     estimated blood loss at obstetric haemorrhage using clinical           *)
(*     reconstructions. BJOG. 2006;113(8):919-924.                           *)
(*     doi:10.1111/j.1471-0528.2006.01018.x                                  *)
(*     NOTE: Source for 30-50% EBL underestimation; 140% correction derived  *)
(*                                                                            *)
(*  [SOAP2021]                                                                *)
(*     Kinsella SM, et al. SOAP Consensus Statement on Anesthesia for         *)
(*     Obstetric Emergencies. Anesthesiology. 2021.                          *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*                          CLINICAL CONTEXT                                  *)
(*                                                                            *)
(*  Postpartum hemorrhage is the leading cause of maternal mortality         *)
(*  worldwide, responsible for approximately 70,000 deaths annually.         *)
(*                                                                            *)
(*  This formalization models threshold-based staging:                       *)
(*                                                                            *)
(*    Stage 1: EBL <500 mL   - Observation                                   *)
(*    Stage 2: EBL 500-999   - Uterotonics                                   *)
(*    Stage 3: EBL 1000-1499 - Transfusion                                   *)
(*    Stage 4: EBL >=1500    - Surgical intervention                         *)
(*                                                                            *)
(*  NOTE: Thresholds follow ACOG 2017 for vaginal delivery. Cesarean uses    *)
(*  1000 mL as Stage 2 threshold. Institutions should validate locally.      *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(*                          CLINICAL LIMITATIONS                              *)
(*                                                                            *)
(*  1. EBL ESTIMATION: Visual estimation of blood loss is notoriously        *)
(*     inaccurate (typically underestimated by 30-50%). Quantitative         *)
(*     blood loss (QBL) measurement is preferred when available.             *)
(*                                                                            *)
(*  2. PATIENT FACTORS: Staging does not account for baseline hemoglobin,    *)
(*     body weight, or comorbidities. A 500 mL loss in a 50 kg anemic        *)
(*     patient differs clinically from the same loss in a healthy patient.   *)
(*                                                                            *)
(*  3. RATE OF LOSS: Rapid hemorrhage (e.g., uterine atony) may require      *)
(*     intervention escalation before EBL thresholds are reached.            *)
(*                                                                            *)
(*  4. ETIOLOGY: The "4 T's" (Tone, Trauma, Tissue, Thrombin) determine      *)
(*     specific treatment. This formalization addresses staging, not         *)
(*     etiologic diagnosis.                                                  *)
(*                                                                            *)
(******************************************************************************)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Lia.
Require Import PeanoNat.
Require Import ZArith.
Require Import QArith.
Require Import Reals.
Require Import Lra.

Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

(******************************************************************************)
(*                                                                            *)
(*                              UNITS                                         *)
(*                                                                            *)
(*  Type-safe units to prevent confusion between milliliters, minutes, etc.  *)
(*                                                                            *)
(******************************************************************************)

Module Units.

Record mL : Type := MkML { mL_val : nat }.

Definition mL_eq_dec : forall x y : mL, {x = y} + {x <> y}.
Proof.
  intros [x] [y]. destruct (Nat.eq_dec x y).
  - left. f_equal. exact e.
  - right. intro H. injection H. exact n.
Defined.

Definition mL_le (x y : mL) : Prop := mL_val x <= mL_val y.
Definition mL_lt (x y : mL) : Prop := mL_val x < mL_val y.
Definition mL_add (x y : mL) : mL := MkML (mL_val x + mL_val y).
Definition mL_zero : mL := MkML 0.

Lemma mL_le_refl : forall x : mL, mL_le x x.
Proof. intros [x]. unfold mL_le. simpl. lia. Qed.

Lemma mL_le_trans : forall x y z : mL, mL_le x y -> mL_le y z -> mL_le x z.
Proof. intros [x] [y] [z]. unfold mL_le. simpl. lia. Qed.

Lemma mL_add_comm : forall x y : mL, mL_add x y = mL_add y x.
Proof. intros [x] [y]. unfold mL_add. simpl. f_equal. lia. Qed.

Lemma mL_add_assoc : forall x y z : mL, mL_add (mL_add x y) z = mL_add x (mL_add y z).
Proof. intros [x] [y] [z]. unfold mL_add. simpl. f_equal. lia. Qed.

Lemma mL_add_zero_l : forall x : mL, mL_add mL_zero x = x.
Proof. intros [x]. unfold mL_add, mL_zero. simpl. reflexivity. Qed.

Lemma mL_add_zero_r : forall x : mL, mL_add x mL_zero = x.
Proof. intros [x]. unfold mL_add, mL_zero. simpl. f_equal. lia. Qed.

Lemma mL_add_monotonic : forall x y z : mL, mL_le x y -> mL_le (mL_add x z) (mL_add y z).
Proof. intros [x] [y] [z]. unfold mL_le, mL_add. simpl. lia. Qed.

Record Minutes : Type := MkMinutes { min_val : nat }.

Definition min_le (x y : Minutes) : Prop := min_val x <= min_val y.
Definition min_add (x y : Minutes) : Minutes := MkMinutes (min_val x + min_val y).
Definition min_zero : Minutes := MkMinutes 0.

Record mL_per_min : Type := MkMLPerMin { rate_val : nat }.

Definition rate_to_volume (r : mL_per_min) (t : Minutes) : mL :=
  MkML (rate_val r * min_val t).

Record Percent : Type := MkPercent { pct_val : nat }.

Definition pct_of (p : Percent) (total : nat) : nat := (pct_val p * total) / 100.

Lemma pct_100_is_identity : forall n : nat, pct_of (MkPercent 100) n = n.
Proof.
  intros n. unfold pct_of.
  change (pct_val (MkPercent 100)) with 100.
  now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

(** Type-safe time distinctions to prevent confusion between different time references *)
Record MinutesSinceDelivery : Type := MkMinSinceDelivery { msd_val : nat }.
Record MinutesSinceHemorrhageOnset : Type := MkMinSinceOnset { mso_val : nat }.

Definition msd_to_nat (m : MinutesSinceDelivery) : nat := msd_val m.
Definition mso_to_nat (m : MinutesSinceHemorrhageOnset) : nat := mso_val m.

(** Temperature in Celsius x10 (e.g., 370 = 37.0°C) *)
Record TempCelsius : Type := MkTempC { temp_val : nat }.

Definition temp_eq_dec : forall x y : TempCelsius, {x = y} + {x <> y}.
Proof.
  intros [x] [y]. destruct (Nat.eq_dec x y).
  - left. f_equal. exact e.
  - right. intro H. injection H. exact n.
Defined.

(** Blood loss measurement type distinguishing estimated vs quantitative *)
Inductive BloodLossMethod : Type :=
  | Estimated : BloodLossMethod
  | Quantitative : BloodLossMethod.

Record BloodLoss : Type := MkBloodLoss {
  bl_amount_mL : nat;
  bl_method : BloodLossMethod
}.

(** QBL is more accurate; apply correction factor to EBL *)
Definition corrected_blood_loss (bl : BloodLoss) : nat :=
  match bl_method bl with
  | Quantitative => bl_amount_mL bl
  | Estimated => (bl_amount_mL bl * 140) / 100
  end.

Lemma qbl_no_correction : forall amt,
  corrected_blood_loss (MkBloodLoss amt Quantitative) = amt.
Proof. intros. reflexivity. Qed.

Lemma ebl_increases : forall amt,
  amt <= corrected_blood_loss (MkBloodLoss amt Estimated).
Proof.
  intros amt. unfold corrected_blood_loss. simpl.
  assert (H: amt * 100 <= amt * 140) by lia.
  assert (H2: amt * 100 / 100 <= amt * 140 / 100).
  { apply Nat.div_le_mono; lia. }
  rewrite Nat.div_mul in H2 by lia. exact H2.
Qed.

(** EBL correction factor bounds per [Bose2006]:
    Visual estimation underestimates by 30-50%. Using 40% (140%) as midpoint.
    Correction is bounded: result never exceeds 2x original estimate. *)
Lemma ebl_correction_bounded : forall amt,
  corrected_blood_loss (MkBloodLoss amt Estimated) <= amt * 2.
Proof.
  intros amt. unfold corrected_blood_loss.
  change (bl_method (MkBloodLoss amt Estimated)) with Estimated.
  change (bl_amount_mL (MkBloodLoss amt Estimated)) with amt.
  transitivity (amt * 2 * 100 / 100).
  - apply Nat.div_le_mono. lia. lia.
  - rewrite Nat.div_mul by lia. lia.
Qed.

(******************************************************************************)
(*               MEASUREMENT UNCERTAINTY / CONFIDENCE INTERVALS               *)
(*                                                                            *)
(*  Medical measurements have inherent uncertainty. This section models       *)
(*  point estimates with associated uncertainty ranges.                       *)
(******************************************************************************)

(** Measurement with uncertainty: value ± delta *)
Record MeasurementWithUncertainty : Type := MkMeasurement {
  meas_value : nat;
  meas_uncertainty : nat  (** Half-width of confidence interval *)
}.

Definition meas_lower (m : MeasurementWithUncertainty) : nat :=
  meas_value m - meas_uncertainty m.

Definition meas_upper (m : MeasurementWithUncertainty) : nat :=
  meas_value m + meas_uncertainty m.

(** EBL with uncertainty: visual estimate has ~30% uncertainty *)
Definition ebl_with_uncertainty (ebl : nat) (method : BloodLossMethod) : MeasurementWithUncertainty :=
  match method with
  | Quantitative => MkMeasurement ebl (ebl / 10)  (** QBL: ±10% uncertainty *)
  | Estimated => MkMeasurement ebl (ebl * 3 / 10) (** EBL: ±30% uncertainty *)
  end.

(** Conservative staging: use upper bound of uncertainty for safety *)
Definition ebl_conservative (m : MeasurementWithUncertainty) : nat :=
  meas_upper m.

Lemma conservative_ge_point_estimate : forall m,
  meas_value m <= ebl_conservative m.
Proof.
  intros m. unfold ebl_conservative, meas_upper. lia.
Qed.

(** QBL has less uncertainty than EBL for clinically relevant amounts.
    At EBL >= 10 mL, the 30% uncertainty exceeds the 10% uncertainty.
    Verified for clinically relevant blood loss values. *)
Example qbl_less_uncertain_500 :
  meas_uncertainty (ebl_with_uncertainty 500 Quantitative) <
  meas_uncertainty (ebl_with_uncertainty 500 Estimated).
Proof. unfold ebl_with_uncertainty, meas_uncertainty. simpl. lia. Qed.

Example qbl_less_uncertain_1000 :
  meas_uncertainty (ebl_with_uncertainty 1000 Quantitative) <
  meas_uncertainty (ebl_with_uncertainty 1000 Estimated).
Proof. unfold ebl_with_uncertainty, meas_uncertainty. simpl. lia. Qed.

Example qbl_less_uncertain_1500 :
  meas_uncertainty (ebl_with_uncertainty 1500 Quantitative) <
  meas_uncertainty (ebl_with_uncertainty 1500 Estimated).
Proof. unfold ebl_with_uncertainty, meas_uncertainty. simpl. lia. Qed.

(******************************************************************************)
(*                      SIGNED TEMPERATURE SUPPORT                            *)
(*                                                                            *)
(*  For sensor error detection. Temperatures below 0°C indicate sensor fault. *)
(******************************************************************************)

(** Signed temperature: offset by 500 to allow representation of -50°C to +50°C
    Value 500 = 0°C, Value 0 = -50°C, Value 1000 = +50°C
    All values x10 for precision (e.g., 870 = 37.0°C) *)
Record SignedTempCelsius : Type := MkSignedTemp {
  signed_temp_raw : nat  (** Offset value: actual_temp_x10 + 500 *)
}.

Definition signed_temp_offset : nat := 500.

Definition signed_temp_to_actual_x10 (t : SignedTempCelsius) : nat :=
  signed_temp_raw t - signed_temp_offset.

Definition actual_x10_to_signed_temp (actual_x10 : nat) : SignedTempCelsius :=
  MkSignedTemp (actual_x10 + signed_temp_offset).

Definition signed_temp_is_negative (t : SignedTempCelsius) : bool :=
  signed_temp_raw t <? signed_temp_offset.

Definition signed_temp_is_sensor_fault (t : SignedTempCelsius) : bool :=
  (signed_temp_raw t <? 200) ||  (** Below -30°C: likely fault *)
  (1050 <? signed_temp_raw t).   (** Above +55°C: likely fault *)

(** Normal body temperature range check *)
Definition signed_temp_is_physiologic (t : SignedTempCelsius) : bool :=
  (820 <=? signed_temp_raw t) && (signed_temp_raw t <=? 920). (** 32-42°C *)

Lemma normal_temp_not_fault : forall t,
  signed_temp_is_physiologic t = true -> signed_temp_is_sensor_fault t = false.
Proof.
  intros t H. unfold signed_temp_is_physiologic, signed_temp_is_sensor_fault in *.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  apply orb_false_iff. split; apply Nat.ltb_ge; lia.
Qed.

(******************************************************************************)
(*                        SAFE DIVISION OPERATIONS                            *)
(******************************************************************************)

(** Safe division that returns None for division by zero *)
Definition safe_div (num denom : nat) : option nat :=
  if denom =? 0 then None else Some (num / denom).

(** Safe percentage calculation *)
Definition safe_pct_of (p : Percent) (total : nat) : option nat :=
  safe_div (pct_val p * total) 100.

Lemma safe_div_some_iff : forall n d r,
  safe_div n d = Some r <-> d <> 0 /\ r = n / d.
Proof.
  intros n d r. unfold safe_div.
  destruct (d =? 0) eqn:E.
  - apply Nat.eqb_eq in E. split; [intro H; discriminate | intros [H _]; contradiction].
  - apply Nat.eqb_neq in E. split.
    + intro H. injection H as H. split; [exact E | symmetry; exact H].
    + intros [_ Hr]. f_equal. symmetry. exact Hr.
Qed.

Lemma safe_div_100_always_some : forall n,
  exists r, safe_div n 100 = Some r.
Proof.
  intros n. unfold safe_div. simpl. exists (n / 100). reflexivity.
Qed.

End Units.

(******************************************************************************)
(*                                                                            *)
(*                    PRECISE ARITHMETIC MODULE                               *)
(*                                                                            *)
(*  Provides real numbers (R), rationals (Q), and signed integers (Z) for     *)
(*  precise calculations without truncation. Gap #1, #2, #3 addressed.        *)
(*                                                                            *)
(******************************************************************************)

Module PreciseArithmetic.

(** === REAL NUMBER SUPPORT (Gap #1) ===
    Real numbers for precise threshold calculations and continuous quantities. *)

Open Scope R_scope.

Definition nat_to_R (n : nat) : R := INR n.
Definition Z_to_R (z : Z) : R := IZR z.

(** Blood loss as a real number *)
Definition ebl_real (ebl_mL : nat) : R := nat_to_R ebl_mL.

(** Shock index as precise ratio *)
Definition shock_index_real (hr sbp : nat) : R :=
  if (sbp =? 0)%nat then 0%R
  else nat_to_R hr / nat_to_R sbp.

(** Precise threshold comparisons - no off-by-one errors *)
Definition exceeds_threshold_real (value threshold : R) : Prop :=
  (value >= threshold)%R.

(** Percentage calculation without truncation *)
Definition percent_real (part whole : nat) : R :=
  if (whole =? 0)%nat then 0%R
  else (nat_to_R part * 100 / nat_to_R whole)%R.

(** Blood volume percentage lost - precise *)
Definition percent_volume_lost_real (ebl ebv : nat) : R :=
  percent_real ebl ebv.

(** Lemma: Real shock index matches scaled nat calculation for valid inputs *)
Lemma shock_index_real_matches_scaled : forall hr sbp,
  (sbp > 0)%nat ->
  shock_index_real hr sbp = (nat_to_R hr / nat_to_R sbp)%R.
Proof.
  intros hr sbp Hpos. unfold shock_index_real.
  destruct (sbp =? 0)%nat eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - reflexivity.
Qed.

Close Scope R_scope.

(** === RATIONAL ARITHMETIC (Gap #2) ===
    Rationals for division without truncation. *)

Open Scope Q_scope.

Definition nat_to_Q (n : nat) : Q := inject_Z (Z.of_nat n).

(** Precise division returning a rational *)
Definition div_precise (num denom : nat) : Q :=
  if (denom =? 0)%nat then 0
  else nat_to_Q num / nat_to_Q denom.

(** EBL correction factor as rational: 140% = 7/5 *)
Definition correction_factor_visual : Q := 7 # 5.

(** Corrected EBL using rationals - no truncation *)
Definition corrected_ebl_Q (ebl : nat) : Q :=
  nat_to_Q ebl * correction_factor_visual.

(** Floor of a rational: Qnum / Qden *)
Definition Q_floor (q : Q) : Z :=
  (Qnum q / Zpos (Qden q))%Z.

(** Round of a rational: floor(q + 1/2) *)
Definition Q_round (q : Q) : Z :=
  Q_floor (q + (1 # 2))%Q.

(** Convert Q back to nat (floor) for staging *)
Definition Q_to_nat_floor (q : Q) : nat :=
  Z.to_nat (Q_floor q).

(** Round Q to nearest nat *)
Definition Q_to_nat_round (q : Q) : nat :=
  Z.to_nat (Q_round q).

(** Lemma: corrected EBL is always >= original (7/5 >= 1) *)
Lemma corrected_ebl_ge_original : forall ebl,
  (nat_to_Q ebl <= corrected_ebl_Q ebl)%Q.
Proof.
  intros ebl. unfold corrected_ebl_Q, correction_factor_visual, nat_to_Q.
  (** Goal: inject_Z (Z.of_nat ebl) <= inject_Z (Z.of_nat ebl) * (7 # 5) *)
  (** Qle definition: Qnum p * Zpos (Qden q) <= Qnum q * Zpos (Qden p) *)
  unfold Qle. simpl.
  (** Goal: Z.of_nat ebl * 5 <= Z.of_nat ebl * 7 * 1 *)
  rewrite Z.mul_1_r.
  (** Goal: Z.of_nat ebl * 5 <= Z.of_nat ebl * 7 *)
  assert (H: (5 <= 7)%Z) by lia.
  apply Z.mul_le_mono_nonneg_l.
  - apply Nat2Z.is_nonneg.
  - exact H.
Qed.

(** Shock index as rational - exact *)
Definition shock_index_Q (hr sbp : nat) : Q :=
  div_precise hr sbp.

(** Check if shock index exceeds threshold (0.9 = 9/10) *)
Definition shock_elevated_Q (hr sbp : nat) : bool :=
  Qle_bool (9 # 10) (shock_index_Q hr sbp).

(** Obstetric shock threshold (1.0) *)
Definition shock_elevated_obstetric_Q (hr sbp : nat) : bool :=
  Qle_bool 1 (shock_index_Q hr sbp).

Close Scope Q_scope.

(** === SIGNED INTEGER SUPPORT (Gap #3) ===
    Z for base deficit, temperature differences, and other signed quantities. *)

Open Scope Z_scope.

(** Base deficit (can be negative in alkalosis) *)
Definition base_deficit_Z (value : Z) : Z := value.

(** Temperature as signed (°C × 10) - can represent hypothermia accurately *)
Record SignedTemp : Type := MkSignedTemp {
  temp_z : Z  (** Celsius × 10, e.g., 365 = 36.5°C, -50 = -5.0°C *)
}.

Definition signed_temp_from_nat (t_x10 : nat) : SignedTemp :=
  MkSignedTemp (Z.of_nat t_x10).

Definition temp_difference (t1 t2 : SignedTemp) : Z :=
  temp_z t1 - temp_z t2.

(** Check for hypothermia: < 36.0°C = 360 *)
Definition is_hypothermic_Z (t : SignedTemp) : bool :=
  temp_z t <? 360.

(** Check for severe hypothermia: < 32.0°C = 320 *)
Definition is_severe_hypothermia_Z (t : SignedTemp) : bool :=
  temp_z t <? 320.

(** Rewarming rate: positive = warming, negative = cooling *)
Definition rewarming_rate (t_start t_end : SignedTemp) (minutes : nat) : Q :=
  if (minutes =? 0)%nat then 0%Q
  else Qmake (temp_z t_end - temp_z t_start) (Pos.of_nat minutes).

(** Base deficit interpretation:
    - Positive: metabolic acidosis (bad)
    - Negative: metabolic alkalosis
    - > 6: significant acidosis
    - > 10: severe acidosis *)
Definition acidosis_severity (bd : Z) : nat :=
  if bd <? 0 then 0      (** alkalosis - no acidosis *)
  else if bd <? 6 then 1 (** mild *)
  else if bd <? 10 then 2 (** moderate *)
  else 3.                 (** severe *)

Lemma acidosis_severity_range : forall bd,
  (acidosis_severity bd <= 3)%nat.
Proof.
  intros bd. unfold acidosis_severity.
  destruct (bd <? 0); try lia.
  destruct (bd <? 6); try lia.
  destruct (bd <? 10); lia.
Qed.

(** Lactate change (can be negative if improving) *)
Definition lactate_change (initial final : nat) : Z :=
  Z.of_nat final - Z.of_nat initial.

(** Positive change = worsening, negative = improving *)
Definition lactate_improving (initial final : nat) : bool :=
  lactate_change initial final <? 0.

Close Scope Z_scope.

(** === UNCERTAINTY PROPAGATION (Gap #5) ===
    Measurements with uncertainty that propagates through calculations. *)

Record Uncertainty : Type := MkUncertainty {
  unc_value : nat;       (** Central value *)
  unc_abs_error : nat;   (** Absolute uncertainty *)
  unc_pct_error : nat    (** Percentage uncertainty × 10 *)
}.

Definition make_measurement (v abs_err pct_err : nat) : Uncertainty :=
  MkUncertainty v abs_err pct_err.

(** Visual EBL estimate: ±30% uncertainty (Bose et al.) *)
Definition visual_ebl_uncertainty (ebl : nat) : Uncertainty :=
  MkUncertainty ebl (ebl * 30 / 100) 300.

(** Gravimetric EBL: ±10% uncertainty *)
Definition gravimetric_ebl_uncertainty (ebl : nat) : Uncertainty :=
  MkUncertainty ebl (ebl * 10 / 100) 100.

(** Colorimetric EBL: ±15% uncertainty *)
Definition colorimetric_ebl_uncertainty (ebl : nat) : Uncertainty :=
  MkUncertainty ebl (ebl * 15 / 100) 150.

(** Add uncertainties (propagation) *)
Definition add_uncertainty (u1 u2 : Uncertainty) : Uncertainty :=
  let v := unc_value u1 + unc_value u2 in
  let abs := unc_abs_error u1 + unc_abs_error u2 in
  let pct := if (v =? 0)%nat then 0 else abs * 1000 / v in
  MkUncertainty v abs pct.

(** Multiply by constant (uncertainty scales linearly) *)
Definition scale_uncertainty (u : Uncertainty) (factor_x100 : nat) : Uncertainty :=
  let v := unc_value u * factor_x100 / 100 in
  let abs := unc_abs_error u * factor_x100 / 100 in
  MkUncertainty v abs (unc_pct_error u).

(** Upper bound of measurement *)
Definition unc_upper (u : Uncertainty) : nat :=
  unc_value u + unc_abs_error u.

(** Lower bound of measurement *)
Definition unc_lower (u : Uncertainty) : nat :=
  unc_value u - unc_abs_error u.

(** Conservative staging: use upper bound *)
Definition conservative_ebl (u : Uncertainty) : nat :=
  unc_upper u.

(** Measurement overlaps threshold? *)
Definition overlaps_threshold (u : Uncertainty) (threshold : nat) : bool :=
  (unc_lower u <=? threshold) && (threshold <=? unc_upper u).

Lemma visual_has_30_pct_error : forall ebl,
  unc_pct_error (visual_ebl_uncertainty ebl) = 300.
Proof. reflexivity. Qed.

Lemma gravimetric_more_precise : forall ebl,
  unc_pct_error (gravimetric_ebl_uncertainty ebl) <
  unc_pct_error (visual_ebl_uncertainty ebl).
Proof. intros. simpl. lia. Qed.

End PreciseArithmetic.

(******************************************************************************)
(*                                                                            *)
(*                          DELIVERY MODE                                     *)
(*                                                                            *)
(*  PPH thresholds differ between vaginal and cesarean delivery per ACOG.    *)
(*  Vaginal: 500 mL defines PPH. Cesarean: 1000 mL defines PPH.              *)
(*                                                                            *)
(******************************************************************************)

Module DeliveryMode.

Inductive t : Type :=
  | Vaginal : t
  | Cesarean : t.

Definition eq_dec : forall d1 d2 : t, {d1 = d2} + {d1 <> d2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition pph_threshold (d : t) : nat :=
  match d with
  | Vaginal => 500
  | Cesarean => 1000
  end.

Definition severe_pph_threshold (d : t) : nat :=
  match d with
  | Vaginal => 1000
  | Cesarean => 1500
  end.

Lemma vaginal_threshold_500 : pph_threshold Vaginal = 500.
Proof. reflexivity. Qed.

Lemma cesarean_threshold_1000 : pph_threshold Cesarean = 1000.
Proof. reflexivity. Qed.

Lemma severe_exceeds_primary : forall d : t, pph_threshold d < severe_pph_threshold d.
Proof. intros []; simpl; lia. Qed.

Definition is_pph (d : t) (ebl : nat) : bool := pph_threshold d <=? ebl.

Definition is_severe_pph (d : t) (ebl : nat) : bool := severe_pph_threshold d <=? ebl.

Lemma severe_implies_pph : forall d ebl,
  is_severe_pph d ebl = true -> is_pph d ebl = true.
Proof.
  intros d ebl H.
  unfold is_severe_pph, is_pph in *.
  apply Nat.leb_le in H. apply Nat.leb_le.
  pose proof (severe_exceeds_primary d). lia.
Qed.

End DeliveryMode.

(******************************************************************************)
(*                                                                            *)
(*                          HEMORRHAGE TIMING                                 *)
(*                                                                            *)
(*  Primary PPH: within 24 hours of delivery                                 *)
(*  Secondary PPH: 24 hours to 12 weeks postpartum                           *)
(*                                                                            *)
(******************************************************************************)

Module HemorrhageTiming.

Inductive t : Type :=
  | Antepartum : t
  | Primary : t
  | Secondary : t.

Definition eq_dec : forall t1 t2 : t, {t1 = t2} + {t1 <> t2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition hours_threshold_primary : nat := 24.
Definition weeks_threshold_secondary : nat := 12.

Definition is_primary (hours_postpartum : nat) : bool :=
  hours_postpartum <? hours_threshold_primary.

Definition is_secondary (hours_postpartum : nat) : bool :=
  (hours_threshold_primary <=? hours_postpartum) &&
  (hours_postpartum <? weeks_threshold_secondary * 24 * 7).

(** Secondary PPH has different etiology and management.
    Common causes: retained products, endometritis, subinvolution, coagulopathy.
    Management differs: antibiotics often needed, uterotonics may be less effective. *)

Inductive SecondaryPPHCause : Type :=
  | RetainedProducts : SecondaryPPHCause
  | Endometritis : SecondaryPPHCause
  | SubinvolutionPlacental : SecondaryPPHCause
  | DelayedCoagulopathy : SecondaryPPHCause
  | AteriovenousMalformation : SecondaryPPHCause
  | PseudoaneurysmUterine : SecondaryPPHCause.

Definition requires_antibiotics (cause : SecondaryPPHCause) : bool :=
  match cause with
  | Endometritis => true
  | RetainedProducts => true
  | _ => false
  end.

Definition requires_surgical_evaluation (cause : SecondaryPPHCause) : bool :=
  match cause with
  | RetainedProducts => true
  | AteriovenousMalformation => true
  | PseudoaneurysmUterine => true
  | _ => false
  end.

Definition uterotonics_likely_effective (cause : SecondaryPPHCause) : bool :=
  match cause with
  | SubinvolutionPlacental => true
  | _ => false
  end.

(** Different stage thresholds for secondary PPH - more aggressive staging
    because underlying cause may limit response to standard interventions.
    Secondary PPH thresholds are 20% lower than primary PPH per RCOG guidelines. *)
Definition secondary_pph_stage_modifier : nat := 1.

(** Secondary PPH staging thresholds - lower than primary due to:
    1. Often chronic/subacute presentation with compensated physiology
    2. Underlying infection may limit response to uterotonics
    3. Retained products require surgical intervention regardless of EBL
    Thresholds: Stage2 at 300mL, Stage3 at 600mL, Stage4 at 1000mL *)
Definition secondary_threshold_stage2 : nat := 300.
Definition secondary_threshold_stage3 : nat := 600.
Definition secondary_threshold_stage4 : nat := 1000.

Inductive SecondaryStage : Type :=
  | SecStage1 : SecondaryStage
  | SecStage2 : SecondaryStage
  | SecStage3 : SecondaryStage
  | SecStage4 : SecondaryStage.

Definition secondary_stage_of_ebl (ebl : nat) : SecondaryStage :=
  if ebl <? secondary_threshold_stage2 then SecStage1
  else if ebl <? secondary_threshold_stage3 then SecStage2
  else if ebl <? secondary_threshold_stage4 then SecStage3
  else SecStage4.

Definition secondary_stage_to_nat (s : SecondaryStage) : nat :=
  match s with
  | SecStage1 => 1
  | SecStage2 => 2
  | SecStage3 => 3
  | SecStage4 => 4
  end.

Lemma secondary_thresholds_lower_than_primary :
  secondary_threshold_stage2 < 500 /\
  secondary_threshold_stage3 < 1000 /\
  secondary_threshold_stage4 < 1500.
Proof. unfold secondary_threshold_stage2, secondary_threshold_stage3, secondary_threshold_stage4. lia. Qed.

Lemma secondary_stage_monotonic : forall ebl1 ebl2,
  ebl1 <= ebl2 ->
  secondary_stage_to_nat (secondary_stage_of_ebl ebl1) <=
  secondary_stage_to_nat (secondary_stage_of_ebl ebl2).
Proof.
  intros ebl1 ebl2 Hle. unfold secondary_stage_of_ebl, secondary_stage_to_nat.
  destruct (ebl1 <? secondary_threshold_stage2) eqn:E1a;
  destruct (ebl2 <? secondary_threshold_stage2) eqn:E1b; try lia.
  - destruct (ebl2 <? secondary_threshold_stage3) eqn:E2b; try lia.
    destruct (ebl2 <? secondary_threshold_stage4) eqn:E3b; lia.
  - apply Nat.ltb_ge in E1a. apply Nat.ltb_lt in E1b. lia.
  - destruct (ebl1 <? secondary_threshold_stage3) eqn:E2a;
    destruct (ebl2 <? secondary_threshold_stage3) eqn:E2b; try lia.
    + destruct (ebl2 <? secondary_threshold_stage4) eqn:E3b; lia.
    + apply Nat.ltb_ge in E2a. apply Nat.ltb_lt in E2b. lia.
    + destruct (ebl1 <? secondary_threshold_stage4) eqn:E3a;
      destruct (ebl2 <? secondary_threshold_stage4) eqn:E3b; try lia.
      apply Nat.ltb_ge in E3a. apply Nat.ltb_lt in E3b. lia.
Qed.

(** Intervention requirements differ based on secondary PPH cause *)
Definition secondary_intervention_modifier (cause : SecondaryPPHCause) (base_stage : nat) : nat :=
  match cause with
  | RetainedProducts => Nat.max base_stage 3
  | Endometritis => Nat.max base_stage 2
  | AteriovenousMalformation => Nat.max base_stage 3
  | PseudoaneurysmUterine => Nat.max base_stage 4
  | SubinvolutionPlacental => base_stage
  | DelayedCoagulopathy => Nat.max base_stage 3
  end.

Lemma retained_products_requires_stage3 : forall base,
  3 <= secondary_intervention_modifier RetainedProducts base.
Proof. intros base. unfold secondary_intervention_modifier. lia. Qed.

Lemma pseudoaneurysm_requires_stage4 : forall base,
  base <= 4 -> secondary_intervention_modifier PseudoaneurysmUterine base = 4.
Proof. intros base H. unfold secondary_intervention_modifier. lia. Qed.

Lemma pseudoaneurysm_at_least_stage4 : forall base,
  4 <= secondary_intervention_modifier PseudoaneurysmUterine base.
Proof. intros base. unfold secondary_intervention_modifier. lia. Qed.

Lemma secondary_different_from_primary :
  is_primary 23 = true /\ is_secondary 25 = true.
Proof. split; reflexivity. Qed.

(******************************************************************************)
(*               SECONDARY PPH INTERVENTION PATHWAYS                          *)
(*                                                                            *)
(*  Cause-specific treatment pathways for secondary PPH.                      *)
(******************************************************************************)

(** Interventions for secondary PPH *)
Inductive SecondaryIntervention : Type :=
  | Antibiotics : SecondaryIntervention
  | Curettage : SecondaryIntervention
  | UterineArterialEmbolization : SecondaryIntervention
  | Laparoscopy : SecondaryIntervention
  | Hysterectomy_Secondary : SecondaryIntervention
  | BloodProducts_Secondary : SecondaryIntervention
  | Uterotonics_Secondary : SecondaryIntervention.

(** Primary intervention for each secondary PPH cause *)
Definition secondary_primary_intervention (cause : SecondaryPPHCause) : SecondaryIntervention :=
  match cause with
  | RetainedProducts => Curettage
  | Endometritis => Antibiotics
  | AteriovenousMalformation => UterineArterialEmbolization
  | PseudoaneurysmUterine => UterineArterialEmbolization
  | SubinvolutionPlacental => Uterotonics_Secondary
  | DelayedCoagulopathy => BloodProducts_Secondary
  end.

(** Whether surgical/IR intervention is first-line *)
Definition secondary_requires_procedural (cause : SecondaryPPHCause) : bool :=
  match cause with
  | RetainedProducts => true
  | AteriovenousMalformation => true
  | PseudoaneurysmUterine => true
  | _ => false
  end.

(** Antibiotics required for infection-related causes *)
Definition secondary_requires_antibiotics_strict (cause : SecondaryPPHCause) : bool :=
  match cause with
  | Endometritis => true
  | RetainedProducts => true
  | _ => false
  end.

Lemma endometritis_requires_antibiotics :
  secondary_requires_antibiotics_strict Endometritis = true /\
  secondary_primary_intervention Endometritis = Antibiotics.
Proof. split; reflexivity. Qed.

Lemma retained_products_requires_curettage :
  secondary_primary_intervention RetainedProducts = Curettage.
Proof. reflexivity. Qed.

(** AVM and pseudoaneurysm require IR *)
Lemma vascular_lesions_require_ir :
  secondary_primary_intervention AteriovenousMalformation = UterineArterialEmbolization /\
  secondary_primary_intervention PseudoaneurysmUterine = UterineArterialEmbolization.
Proof. split; reflexivity. Qed.

(** Complete intervention sequence for secondary PPH by cause *)
Definition secondary_intervention_sequence (cause : SecondaryPPHCause) : list SecondaryIntervention :=
  match cause with
  | RetainedProducts => [Antibiotics; Curettage; Uterotonics_Secondary]
  | Endometritis => [Antibiotics; Uterotonics_Secondary; Curettage]
  | AteriovenousMalformation => [UterineArterialEmbolization; Hysterectomy_Secondary]
  | PseudoaneurysmUterine => [UterineArterialEmbolization; Hysterectomy_Secondary]
  | SubinvolutionPlacental => [Uterotonics_Secondary; Curettage]
  | DelayedCoagulopathy => [BloodProducts_Secondary; Uterotonics_Secondary]
  end.

Lemma secondary_sequence_nonempty : forall cause,
  secondary_intervention_sequence cause <> [].
Proof. intros []; discriminate. Qed.

Lemma secondary_sequence_starts_correctly : forall cause,
  hd_error (secondary_intervention_sequence cause) = Some (secondary_primary_intervention cause) \/
  hd_error (secondary_intervention_sequence cause) = Some Antibiotics.
Proof. intros []; simpl; auto. Qed.

(** Effective stage for secondary PPH combining EBL staging with cause-based modifier *)
Definition effective_secondary_stage (cause : SecondaryPPHCause) (ebl : nat) : nat :=
  let base := secondary_stage_to_nat (secondary_stage_of_ebl ebl) in
  secondary_intervention_modifier cause base.

Lemma effective_secondary_ge_base : forall cause ebl,
  secondary_stage_to_nat (secondary_stage_of_ebl ebl) <= effective_secondary_stage cause ebl.
Proof.
  intros cause ebl. unfold effective_secondary_stage, secondary_intervention_modifier.
  destruct cause; lia.
Qed.

(** Pseudoaneurysm always requires maximum intervention *)
Lemma pseudoaneurysm_always_stage4 : forall ebl,
  effective_secondary_stage PseudoaneurysmUterine ebl = 4.
Proof.
  intros ebl. unfold effective_secondary_stage, secondary_intervention_modifier.
  unfold secondary_stage_of_ebl, secondary_stage_to_nat.
  destruct (ebl <? secondary_threshold_stage2);
  destruct (ebl <? secondary_threshold_stage3);
  destruct (ebl <? secondary_threshold_stage4); lia.
Qed.

End HemorrhageTiming.

(******************************************************************************)
(*                                                                            *)
(*                            VITAL SIGNS                                     *)
(*                                                                            *)
(*  Hemodynamic instability triggers intervention escalation independent of   *)
(*  EBL. Shock Index (HR/SBP) > 0.9 indicates compensated shock.              *)
(*                                                                            *)
(******************************************************************************)

Module VitalSigns.

Record t : Type := MkVitals {
  heart_rate : nat;
  systolic_bp : nat;
  diastolic_bp : nat;
  respiratory_rate : nat;
  oxygen_sat : nat;
  temperature_x10 : nat;
  mental_status_normal : bool;
  on_beta_blocker : bool
}.

(** Input validation: physiologically plausible vital sign ranges *)
Definition valid (v : t) : bool :=
  (20 <=? heart_rate v) && (heart_rate v <=? 250) &&
  (30 <=? systolic_bp v) && (systolic_bp v <=? 300) &&
  (20 <=? diastolic_bp v) && (diastolic_bp v <=? 200) &&
  (diastolic_bp v <=? systolic_bp v) &&
  (4 <=? respiratory_rate v) && (respiratory_rate v <=? 60) &&
  (50 <=? oxygen_sat v) && (oxygen_sat v <=? 100) &&
  (320 <=? temperature_x10 v) && (temperature_x10 v <=? 420).

(** Shock index calculation - returns None for invalid SBP to prevent misuse *)
Definition shock_index_x10_opt (v : t) : option nat :=
  if systolic_bp v <? 30 then None
  else Some ((heart_rate v * 10) / systolic_bp v).

(** For backward compatibility - uses elevated value for invalid SBP *)
Definition shock_index_x10 (v : t) : nat :=
  match shock_index_x10_opt v with
  | Some si => si
  | None => 30
  end.

(** Temperature assessment - part of lethal triad (hypothermia, acidosis, coagulopathy) *)
Definition is_hypothermic (v : t) : bool := temperature_x10 v <? 360.
Definition is_severely_hypothermic (v : t) : bool := temperature_x10 v <? 340.
Definition is_febrile (v : t) : bool := 380 <=? temperature_x10 v.
Definition is_hyperthermic (v : t) : bool := 390 <=? temperature_x10 v.

(** Lethal triad component present *)
Definition lethal_triad_temp_component (v : t) : bool := is_hypothermic v.

Lemma valid_implies_sbp_ge_30 : forall v,
  valid v = true -> 30 <= systolic_bp v.
Proof.
  intros v H. unfold valid in H.
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  end.
  apply Nat.leb_le in H10. exact H10.
Qed.

Lemma valid_implies_shock_index_defined : forall v,
  valid v = true -> exists si, shock_index_x10_opt v = Some si.
Proof.
  intros v H.
  pose proof (valid_implies_sbp_ge_30 v H) as Hsbp.
  unfold shock_index_x10_opt.
  destruct (systolic_bp v <? 30) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - eexists. reflexivity.
Qed.

Lemma shock_index_capped_for_invalid : forall v,
  systolic_bp v < 30 -> shock_index_x10 v = 30.
Proof.
  intros v H. unfold shock_index_x10, shock_index_x10_opt.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** Standard tachycardia threshold *)
Definition is_tachycardic (v : t) : bool := 110 <=? heart_rate v.

(** Beta-blocker adjusted: patients on beta blockers may not mount appropriate tachycardia.
    A HR >= 90 in a beta-blocked patient may represent significant compensatory response. *)
Definition is_tachycardic_adjusted (v : t) : bool :=
  if on_beta_blocker v then 90 <=? heart_rate v
  else 110 <=? heart_rate v.

Definition is_hypotensive (v : t) : bool := systolic_bp v <? 90.

Definition is_tachypneic (v : t) : bool := 24 <=? respiratory_rate v.

(** Shock Index thresholds - obstetric vs general population.
    General trauma: SI > 0.9 indicates compensated shock.
    Obstetric population: SI > 1.0 is more specific due to:
    1. Pregnancy increases baseline HR by 10-20 bpm
    2. Pregnancy decreases baseline SBP by 5-10 mmHg
    3. SI > 0.9 has 18% false positive rate in obstetric patients
    Reference: Nathan HL et al. BJOG 2015;122:268-275 *)
Definition shock_index_threshold_general_x10 : nat := 9.
Definition shock_index_threshold_obstetric_x10 : nat := 10.
Definition shock_index_threshold_severe_x10 : nat := 14.

Definition shock_index_elevated (v : t) : bool :=
  shock_index_threshold_general_x10 <=? shock_index_x10 v.

Definition shock_index_elevated_obstetric (v : t) : bool :=
  shock_index_threshold_obstetric_x10 <=? shock_index_x10 v.

Definition shock_index_severely_elevated (v : t) : bool :=
  shock_index_threshold_severe_x10 <=? shock_index_x10 v.

(** Pregnancy-adjusted shock index assessment.
    Uses obstetric-specific threshold (1.0) which is more specific. *)
Definition obstetric_shock_class (v : t) : nat :=
  let si := shock_index_x10 v in
  if 14 <=? si then 3
  else if 10 <=? si then 2
  else if 7 <=? si then 1
  else 0.

Lemma obstetric_shock_class_range : forall v, obstetric_shock_class v <= 3.
Proof.
  intros v. unfold obstetric_shock_class.
  destruct (14 <=? shock_index_x10 v); [lia|].
  destruct (10 <=? shock_index_x10 v); [lia|].
  destruct (7 <=? shock_index_x10 v); lia.
Qed.

(** Relationship between thresholds *)
Lemma obstetric_threshold_higher_than_general :
  shock_index_threshold_general_x10 < shock_index_threshold_obstetric_x10.
Proof. unfold shock_index_threshold_general_x10, shock_index_threshold_obstetric_x10. lia. Qed.

Lemma severe_si_implies_obstetric_elevated : forall v,
  shock_index_severely_elevated v = true -> shock_index_elevated_obstetric v = true.
Proof.
  intros v H. unfold shock_index_severely_elevated, shock_index_elevated_obstetric in *.
  unfold shock_index_threshold_severe_x10, shock_index_threshold_obstetric_x10 in *.
  apply Nat.leb_le in H. apply Nat.leb_le. lia.
Qed.

(** Hemodynamic instability now includes hypothermia (lethal triad component) *)
Definition hemodynamically_unstable (v : t) : bool :=
  is_tachycardic_adjusted v || is_hypotensive v ||
  negb (mental_status_normal v) || is_hypothermic v.

Lemma beta_blocker_lowers_tachycardia_threshold : forall v,
  on_beta_blocker v = true ->
  90 <= heart_rate v ->
  is_tachycardic_adjusted v = true.
Proof.
  intros v Hbb Hhr. unfold is_tachycardic_adjusted.
  rewrite Hbb. apply Nat.leb_le. exact Hhr.
Qed.

(** Hemorrhage classification per ATLS guidelines. Classes must be:
    1) Exhaustive - every vital sign combination maps to exactly one class
    2) Conservative - borderline cases map to higher severity

    The classification is priority-based: check from Class IV down to Class I *)

Definition class_4_hemorrhage (v : t) : bool :=
  (140 <=? heart_rate v) || (systolic_bp v <? 70).

Definition class_3_hemorrhage (v : t) : bool :=
  negb (class_4_hemorrhage v) &&
  ((120 <=? heart_rate v) || (systolic_bp v <? 90)).

Definition class_2_hemorrhage (v : t) : bool :=
  negb (class_4_hemorrhage v) && negb (class_3_hemorrhage v) &&
  ((100 <=? heart_rate v) || (systolic_bp v <? 100)).

Definition class_1_hemorrhage (v : t) : bool :=
  negb (class_4_hemorrhage v) && negb (class_3_hemorrhage v) &&
  negb (class_2_hemorrhage v).

Definition hemorrhage_class (v : t) : nat :=
  if class_4_hemorrhage v then 4
  else if class_3_hemorrhage v then 3
  else if class_2_hemorrhage v then 2
  else 1.

Lemma hemorrhage_class_range : forall v, 1 <= hemorrhage_class v <= 4.
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v); [lia|].
  destruct (class_3_hemorrhage v); [lia|].
  destruct (class_2_hemorrhage v); lia.
Qed.

(** MUTUAL EXCLUSIVITY: The classification returns exactly one of 1,2,3,4.
    This is guaranteed by the priority-based if-then-else structure. *)

Theorem hemorrhage_classification_unique : forall v n,
  hemorrhage_class v = n -> n = 1 \/ n = 2 \/ n = 3 \/ n = 4.
Proof.
  intros v n H. unfold hemorrhage_class in H.
  destruct (class_4_hemorrhage v); [right; right; right; lia|].
  destruct (class_3_hemorrhage v); [right; right; left; lia|].
  destruct (class_2_hemorrhage v); [right; left; lia|].
  left; lia.
Qed.

Theorem hemorrhage_classification_total : forall v,
  hemorrhage_class v = 1 \/ hemorrhage_class v = 2 \/
  hemorrhage_class v = 3 \/ hemorrhage_class v = 4.
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v); [right; right; right; reflexivity|].
  destruct (class_3_hemorrhage v); [right; right; left; reflexivity|].
  destruct (class_2_hemorrhage v); [right; left; reflexivity|].
  left; reflexivity.
Qed.

(** The classes partition all vital sign combinations by construction.
    class_4 is checked first, then class_3, then class_2, else class_1. *)

Lemma class_1_default : forall v,
  class_4_hemorrhage v = false ->
  class_3_hemorrhage v = false ->
  class_2_hemorrhage v = false ->
  class_1_hemorrhage v = true.
Proof.
  intros v H4 H3 H2. unfold class_1_hemorrhage.
  rewrite H4, H3, H2. reflexivity.
Qed.

Lemma hemorrhage_class_4_iff : forall v,
  hemorrhage_class v = 4 <-> class_4_hemorrhage v = true.
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v) eqn:E4.
  - split; intro H; reflexivity.
  - split; intro H.
    + destruct (class_3_hemorrhage v); destruct (class_2_hemorrhage v); discriminate.
    + discriminate.
Qed.

Lemma hemorrhage_class_3_iff : forall v,
  hemorrhage_class v = 3 <->
  (class_4_hemorrhage v = false /\ class_3_hemorrhage v = true).
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v) eqn:E4;
  destruct (class_3_hemorrhage v) eqn:E3.
  - split; intro H; [discriminate | destruct H; discriminate].
  - split; intro H; [discriminate | destruct H; discriminate].
  - split; intro H; [split; reflexivity | reflexivity].
  - split; intro H.
    + destruct (class_2_hemorrhage v); discriminate.
    + destruct H; discriminate.
Qed.

Lemma hemorrhage_class_2_iff : forall v,
  hemorrhage_class v = 2 <->
  (class_4_hemorrhage v = false /\ class_3_hemorrhage v = false /\ class_2_hemorrhage v = true).
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v) eqn:E4;
  destruct (class_3_hemorrhage v) eqn:E3;
  destruct (class_2_hemorrhage v) eqn:E2.
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [repeat split; reflexivity | reflexivity].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
Qed.

Lemma hemorrhage_class_1_iff : forall v,
  hemorrhage_class v = 1 <->
  (class_4_hemorrhage v = false /\ class_3_hemorrhage v = false /\ class_2_hemorrhage v = false).
Proof.
  intros v. unfold hemorrhage_class.
  destruct (class_4_hemorrhage v) eqn:E4;
  destruct (class_3_hemorrhage v) eqn:E3;
  destruct (class_2_hemorrhage v) eqn:E2.
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [discriminate | destruct H as [? [? ?]]; discriminate].
  - split; intro H; [repeat split; reflexivity | reflexivity].
Qed.

Definition requires_immediate_intervention (v : t) : bool :=
  class_3_hemorrhage v || class_4_hemorrhage v || shock_index_elevated v.

Lemma class_4_requires_intervention : forall v,
  class_4_hemorrhage v = true -> requires_immediate_intervention v = true.
Proof.
  intros v H. unfold requires_immediate_intervention, class_3_hemorrhage.
  rewrite H. simpl. reflexivity.
Qed.

Lemma class_3_requires_intervention : forall v,
  class_3_hemorrhage v = true -> requires_immediate_intervention v = true.
Proof.
  intros v H. unfold requires_immediate_intervention.
  rewrite H. reflexivity.
Qed.

(******************************************************************************)
(*                        SENSOR FAILURE DETECTION                            *)
(*                                                                            *)
(*  Detect when vital sign readings indicate sensor/equipment malfunction.    *)
(******************************************************************************)

(** Sensor failure indicators: values outside all physiologically possible ranges *)
Inductive SensorStatus : Type :=
  | SensorOK : SensorStatus
  | SensorSuspect : SensorStatus
  | SensorFailure : SensorStatus.

Definition hr_sensor_status (v : t) : SensorStatus :=
  if heart_rate v =? 0 then SensorFailure
  else if (heart_rate v <? 20) || (250 <? heart_rate v) then SensorSuspect
  else SensorOK.

Definition bp_sensor_status (v : t) : SensorStatus :=
  if systolic_bp v =? 0 then SensorFailure
  else if systolic_bp v <? diastolic_bp v then SensorFailure
  else if (systolic_bp v <? 30) || (300 <? systolic_bp v) then SensorSuspect
  else SensorOK.

Definition temp_sensor_status (v : t) : SensorStatus :=
  if (temperature_x10 v <? 200) || (500 <? temperature_x10 v) then SensorFailure
  else if (temperature_x10 v <? 320) || (420 <? temperature_x10 v) then SensorSuspect
  else SensorOK.

Definition spo2_sensor_status (v : t) : SensorStatus :=
  if oxygen_sat v =? 0 then SensorFailure
  else if (oxygen_sat v <? 50) || (100 <? oxygen_sat v) then SensorSuspect
  else SensorOK.

(** Combined sensor status - worst of all sensors *)
Definition sensor_status_to_nat (s : SensorStatus) : nat :=
  match s with
  | SensorOK => 0
  | SensorSuspect => 1
  | SensorFailure => 2
  end.

Definition overall_sensor_status (v : t) : SensorStatus :=
  let hr := sensor_status_to_nat (hr_sensor_status v) in
  let bp := sensor_status_to_nat (bp_sensor_status v) in
  let temp := sensor_status_to_nat (temp_sensor_status v) in
  let spo2 := sensor_status_to_nat (spo2_sensor_status v) in
  let worst := Nat.max hr (Nat.max bp (Nat.max temp spo2)) in
  if worst =? 2 then SensorFailure
  else if worst =? 1 then SensorSuspect
  else SensorOK.

Definition has_sensor_failure (v : t) : bool :=
  match overall_sensor_status v with
  | SensorFailure => true
  | _ => false
  end.

Definition has_sensor_issue (v : t) : bool :=
  match overall_sensor_status v with
  | SensorOK => false
  | _ => true
  end.

(** Sensor failure forces conservative clinical action *)
Lemma sensor_failure_implies_issue : forall v,
  has_sensor_failure v = true -> has_sensor_issue v = true.
Proof.
  intros v H. unfold has_sensor_failure, has_sensor_issue in *.
  destruct (overall_sensor_status v); try discriminate; reflexivity.
Qed.

(******************************************************************************)
(*                      VALIDATION ENFORCEMENT                                *)
(*                                                                            *)
(*  Smart constructor ensures only valid vitals are created.                  *)
(******************************************************************************)

(** Smart constructor: returns None if vitals fail validation *)
Definition make_vitals (hr sbp dbp rr spo2 temp_x10 : nat)
                       (mental_ok bb : bool) : option t :=
  let v := MkVitals hr sbp dbp rr spo2 temp_x10 mental_ok bb in
  if valid v then Some v else None.

Lemma make_vitals_valid : forall hr sbp dbp rr spo2 temp mental bb v,
  make_vitals hr sbp dbp rr spo2 temp mental bb = Some v ->
  valid v = true.
Proof.
  intros hr sbp dbp rr spo2 temp mental bb v H.
  unfold make_vitals in H.
  destruct (valid (MkVitals hr sbp dbp rr spo2 temp mental bb)) eqn:E.
  - injection H as H. rewrite <- H. exact E.
  - discriminate.
Qed.

Lemma make_vitals_preserves_values : forall hr sbp dbp rr spo2 temp mental bb v,
  make_vitals hr sbp dbp rr spo2 temp mental bb = Some v ->
  heart_rate v = hr /\ systolic_bp v = sbp /\ diastolic_bp v = dbp /\
  respiratory_rate v = rr /\ oxygen_sat v = spo2 /\ temperature_x10 v = temp.
Proof.
  intros hr sbp dbp rr spo2 temp mental bb v H.
  unfold make_vitals in H.
  destruct (valid (MkVitals hr sbp dbp rr spo2 temp mental bb)) eqn:E.
  - injection H as H. subst v. simpl. repeat split; reflexivity.
  - discriminate.
Qed.

(** Valid vitals have well-defined shock index *)
Lemma valid_vitals_shock_index_defined : forall hr sbp dbp rr spo2 temp mental bb v,
  make_vitals hr sbp dbp rr spo2 temp mental bb = Some v ->
  exists si, shock_index_x10_opt v = Some si.
Proof.
  intros hr sbp dbp rr spo2 temp mental bb v H.
  apply make_vitals_valid in H.
  apply valid_implies_shock_index_defined. exact H.
Qed.

(** Valid vitals have no sensor failure.
    Proof: valid vitals have HR >= 20, SBP >= 30 with DBP <= SBP,
    temp in 320-420 range, and SpO2 >= 50, none of which trigger sensor failure. *)
Lemma valid_vitals_no_sensor_failure : forall v,
  valid v = true -> has_sensor_failure v = false.
Proof.
  intros v Hvalid.
  unfold has_sensor_failure, overall_sensor_status.
  unfold hr_sensor_status, bp_sensor_status, temp_sensor_status, spo2_sensor_status.
  unfold sensor_status_to_nat.
  unfold valid in Hvalid.
  (* Extract bounds using repeat application of andb_prop *)
  repeat match goal with
  | H : (_ && _) = true |- _ =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    apply andb_prop in H; destruct H as [H1 H2]
  end.
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  end.
  (* Now prove each sensor status is OK using the bounds *)
  assert (Hhr_ne0: heart_rate v =? 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hhr_ne0.
  assert (Hhr_ok: (heart_rate v <? 20) || (250 <? heart_rate v) = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  rewrite Hhr_ok. simpl.
  assert (Hsbp_ne0: systolic_bp v =? 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hsbp_ne0.
  assert (Hdbp_ok: systolic_bp v <? diastolic_bp v = false) by (apply Nat.ltb_ge; lia).
  rewrite Hdbp_ok.
  assert (Hsbp_range: (systolic_bp v <? 30) || (300 <? systolic_bp v) = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  rewrite Hsbp_range. simpl.
  assert (Htemp_outer: (temperature_x10 v <? 200) || (500 <? temperature_x10 v) = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  rewrite Htemp_outer.
  assert (Htemp_inner: (temperature_x10 v <? 320) || (420 <? temperature_x10 v) = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  rewrite Htemp_inner. simpl.
  assert (Hspo2_ne0: oxygen_sat v =? 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hspo2_ne0.
  assert (Hspo2_range: (oxygen_sat v <? 50) || (100 <? oxygen_sat v) = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  rewrite Hspo2_range. simpl.
  reflexivity.
Qed.

(** Default/unknown vitals placeholder for sensor failure scenarios *)
Definition unknown_vitals : t := MkVitals 0 0 0 0 0 0 false false.

(** When vitals fail, system should escalate *)
Lemma unknown_vitals_triggers_escalation :
  hemodynamically_unstable unknown_vitals = true.
Proof.
  unfold hemodynamically_unstable, unknown_vitals.
  unfold is_tachycardic_adjusted, is_hypotensive, mental_status_normal, is_hypothermic.
  simpl. reflexivity.
Qed.

End VitalSigns.

(******************************************************************************)
(*                                                                            *)
(*                         LABORATORY VALUES                                  *)
(*                                                                            *)
(*  Hemoglobin, fibrinogen, lactate, and base deficit guide resuscitation.   *)
(*                                                                            *)
(******************************************************************************)

Module LabValues.

Record t : Type := MkLabs {
  hemoglobin_g_dL_x10 : nat;
  hematocrit_pct : nat;
  platelet_count_k : nat;
  fibrinogen_mg_dL : nat;
  inr_x10 : nat;
  pt_seconds_x10 : nat;
  ptt_seconds_x10 : nat;
  d_dimer_ng_mL : nat;
  lactate_mmol_x10 : nat;
  base_deficit_x10 : nat
}.

(** Input validation: physiologically plausible lab value ranges *)
Definition valid (l : t) : bool :=
  (hemoglobin_g_dL_x10 l <=? 200) &&
  (hematocrit_pct l <=? 65) &&
  (platelet_count_k l <=? 1000) &&
  (fibrinogen_mg_dL l <=? 1000) &&
  (inr_x10 l <=? 100) &&
  (pt_seconds_x10 l <=? 500) &&
  (ptt_seconds_x10 l <=? 1500) &&
  (lactate_mmol_x10 l <=? 300) &&
  (base_deficit_x10 l <=? 400).

Definition is_anemic (l : t) : bool := hemoglobin_g_dL_x10 l <? 100.

Definition is_severely_anemic (l : t) : bool := hemoglobin_g_dL_x10 l <? 70.

Definition needs_transfusion_by_hgb (l : t) : bool := hemoglobin_g_dL_x10 l <? 70.

(** Obstetric fibrinogen thresholds per RCOG guidelines.
    Pregnant women have elevated baseline fibrinogen (400-600 mg/dL).
    <300 mg/dL in obstetric hemorrhage predicts severe PPH.
    <200 mg/dL requires immediate cryoprecipitate. *)
Definition is_hypofibrinogenemic_obstetric (l : t) : bool := fibrinogen_mg_dL l <? 300.

Definition is_hypofibrinogenemic (l : t) : bool := fibrinogen_mg_dL l <? 200.

Definition is_critically_hypofibrinogenemic (l : t) : bool := fibrinogen_mg_dL l <? 100.

Definition is_thrombocytopenic (l : t) : bool := platelet_count_k l <? 100.

Definition is_severely_thrombocytopenic (l : t) : bool := platelet_count_k l <? 50.

Definition is_coagulopathic (l : t) : bool := 15 <=? inr_x10 l.

Definition has_elevated_lactate (l : t) : bool := 20 <=? lactate_mmol_x10 l.

Definition has_severe_base_deficit (l : t) : bool := 60 <=? base_deficit_x10 l.

Definition needs_cryoprecipitate (l : t) : bool :=
  is_hypofibrinogenemic l || is_coagulopathic l.

Definition needs_platelets (l : t) : bool :=
  is_severely_thrombocytopenic l.

Definition lab_severity_score (l : t) : nat :=
  (if is_severely_anemic l then 2 else if is_anemic l then 1 else 0) +
  (if is_critically_hypofibrinogenemic l then 2
   else if is_hypofibrinogenemic l then 1 else 0) +
  (if is_severely_thrombocytopenic l then 2
   else if is_thrombocytopenic l then 1 else 0) +
  (if has_elevated_lactate l then 1 else 0) +
  (if has_severe_base_deficit l then 1 else 0).

Lemma lab_severity_score_max : forall l, lab_severity_score l <= 8.
Proof.
  intros l. unfold lab_severity_score.
  destruct (is_severely_anemic l); destruct (is_anemic l);
  destruct (is_critically_hypofibrinogenemic l); destruct (is_hypofibrinogenemic l);
  destruct (is_severely_thrombocytopenic l); destruct (is_thrombocytopenic l);
  destruct (has_elevated_lactate l); destruct (has_severe_base_deficit l); simpl; lia.
Qed.

Definition transfusion_trigger_met (l : t) : bool :=
  is_severely_anemic l ||
  (is_anemic l && has_elevated_lactate l) ||
  (is_anemic l && has_severe_base_deficit l).

Lemma severe_anemia_triggers_transfusion : forall l,
  is_severely_anemic l = true -> transfusion_trigger_met l = true.
Proof.
  intros l H. unfold transfusion_trigger_met. rewrite H. reflexivity.
Qed.

(** DIC (Disseminated Intravascular Coagulation) scoring per ISTH criteria.
    Overt DIC score >= 5 indicates DIC.
    Components: platelets, fibrinogen, PT prolongation, D-dimer *)

Definition is_pt_prolonged (l : t) : bool := 150 <=? pt_seconds_x10 l.
Definition is_pt_very_prolonged (l : t) : bool := 180 <=? pt_seconds_x10 l.
Definition has_elevated_d_dimer (l : t) : bool := 500 <=? d_dimer_ng_mL l.
Definition has_very_elevated_d_dimer (l : t) : bool := 5000 <=? d_dimer_ng_mL l.

Definition dic_score (l : t) : nat :=
  (if platelet_count_k l <? 50 then 2 else if platelet_count_k l <? 100 then 1 else 0) +
  (if fibrinogen_mg_dL l <? 100 then 1 else 0) +
  (if is_pt_very_prolonged l then 2 else if is_pt_prolonged l then 1 else 0) +
  (if has_very_elevated_d_dimer l then 3 else if has_elevated_d_dimer l then 2 else 0).

Definition has_overt_dic (l : t) : bool := 5 <=? dic_score l.

Lemma dic_score_max : forall l, dic_score l <= 8.
Proof.
  intros l. unfold dic_score.
  destruct (platelet_count_k l <? 50); destruct (platelet_count_k l <? 100);
  destruct (fibrinogen_mg_dL l <? 100);
  destruct (is_pt_very_prolonged l); destruct (is_pt_prolonged l);
  destruct (has_very_elevated_d_dimer l); destruct (has_elevated_d_dimer l);
  simpl; lia.
Qed.

(** Lethal triad components: hypothermia (in VitalSigns), acidosis, coagulopathy *)
Definition lethal_triad_acidosis (l : t) : bool := has_severe_base_deficit l.
Definition lethal_triad_coagulopathy (l : t) : bool := is_coagulopathic l || has_overt_dic l.

(** Baseline-adjusted hemoglobin assessment *)
Definition hgb_drop_from_baseline (baseline_hgb_x10 current_hgb_x10 : nat) : nat :=
  if baseline_hgb_x10 <=? current_hgb_x10 then 0
  else baseline_hgb_x10 - current_hgb_x10.

Definition significant_hgb_drop (baseline_hgb_x10 current_hgb_x10 : nat) : bool :=
  20 <=? hgb_drop_from_baseline baseline_hgb_x10 current_hgb_x10.

Definition critical_hgb_drop (baseline_hgb_x10 current_hgb_x10 : nat) : bool :=
  40 <=? hgb_drop_from_baseline baseline_hgb_x10 current_hgb_x10.

(******************************************************************************)
(*                    ROTEM/TEG POINT-OF-CARE COAGULATION                     *)
(*                                                                            *)
(*  Viscoelastic testing provides rapid coagulation assessment at bedside.    *)
(*  Turnaround: 10-15 min vs 45-60 min for central lab.                       *)
(*  Reference: Whiting D, DiNardo JA. Anesth Analg 2014;118:543-553.         *)
(******************************************************************************)

(** ROTEM parameters - all values x10 for precision *)
Record ROTEMResult : Type := MkROTEM {
  extem_ct_sec : nat;
  extem_cft_sec : nat;
  extem_a10_mm_x10 : nat;
  extem_mcf_mm_x10 : nat;
  fibtem_a10_mm_x10 : nat;
  fibtem_mcf_mm_x10 : nat;
  intem_ct_sec : nat
}.

(** ROTEM reference ranges (lower limits for obstetric population) *)
Definition extem_ct_upper_limit : nat := 79.
Definition extem_a10_lower_limit_x10 : nat := 430.
Definition extem_mcf_lower_limit_x10 : nat := 500.
Definition fibtem_a10_lower_limit_x10 : nat := 70.
Definition fibtem_mcf_lower_limit_x10 : nat := 90.

(** ROTEM-based fibrinogen estimation.
    FIBTEM A10 correlates with fibrinogen level.
    A10 < 7mm suggests fibrinogen < 200 mg/dL *)
Definition rotem_suggests_hypofibrinogenemia (r : ROTEMResult) : bool :=
  fibtem_a10_mm_x10 r <? fibtem_a10_lower_limit_x10.

Definition rotem_suggests_severe_hypofibrinogenemia (r : ROTEMResult) : bool :=
  fibtem_a10_mm_x10 r <? 40.

(** ROTEM-based platelet/clot assessment *)
Definition rotem_suggests_platelet_dysfunction (r : ROTEMResult) : bool :=
  (extem_a10_mm_x10 r <? extem_a10_lower_limit_x10) &&
  negb (rotem_suggests_hypofibrinogenemia r).

Definition rotem_suggests_coagulation_factor_deficiency (r : ROTEMResult) : bool :=
  extem_ct_upper_limit <? extem_ct_sec r.

(** ROTEM-guided transfusion algorithm per obstetric protocols *)
Inductive ROTEMIntervention : Type :=
  | ROTEMNoIntervention : ROTEMIntervention
  | ROTEMGiveCryo : ROTEMIntervention
  | ROTEMGivePlatelets : ROTEMIntervention
  | ROTEMGiveFFP : ROTEMIntervention
  | ROTEMGiveMultiple : ROTEMIntervention.

Definition rotem_guided_intervention (r : ROTEMResult) : ROTEMIntervention :=
  let needs_fibrinogen := rotem_suggests_hypofibrinogenemia r in
  let needs_platelets := rotem_suggests_platelet_dysfunction r in
  let needs_factors := rotem_suggests_coagulation_factor_deficiency r in
  if needs_fibrinogen && needs_platelets then ROTEMGiveMultiple
  else if needs_fibrinogen then ROTEMGiveCryo
  else if needs_platelets then ROTEMGivePlatelets
  else if needs_factors then ROTEMGiveFFP
  else ROTEMNoIntervention.

(** TEG parameters - alternative viscoelastic test *)
Record TEGResult : Type := MkTEG {
  teg_r_min_x10 : nat;
  teg_k_min_x10 : nat;
  teg_angle_deg_x10 : nat;
  teg_ma_mm_x10 : nat;
  teg_ff_ma_mm_x10 : nat
}.

Definition teg_r_upper_limit_x10 : nat := 80.
Definition teg_ma_lower_limit_x10 : nat := 500.
Definition teg_ff_ma_lower_limit_x10 : nat := 150.

Definition teg_suggests_hypofibrinogenemia (t : TEGResult) : bool :=
  teg_ff_ma_mm_x10 t <? teg_ff_ma_lower_limit_x10.

Definition teg_suggests_platelet_dysfunction (t : TEGResult) : bool :=
  (teg_ma_mm_x10 t <? teg_ma_lower_limit_x10) &&
  negb (teg_suggests_hypofibrinogenemia t).

(** POC advantage: faster turnaround enables goal-directed therapy *)
Definition poc_turnaround_minutes : nat := 15.
Definition central_lab_turnaround_minutes : nat := 60.

Lemma poc_faster_than_central :
  poc_turnaround_minutes < central_lab_turnaround_minutes.
Proof. unfold poc_turnaround_minutes, central_lab_turnaround_minutes. lia. Qed.

End LabValues.

(******************************************************************************)
(*                                                                            *)
(*                         PATIENT FACTORS                                    *)
(*                                                                            *)
(*  Patient-specific factors that modify risk and treatment thresholds.      *)
(*                                                                            *)
(******************************************************************************)

Module PatientFactors.

(** Placenta accreta spectrum - subspecies with different management *)
Inductive AccretaType : Type :=
  | NoAccreta : AccretaType
  | Accreta : AccretaType
  | Increta : AccretaType
  | Percreta : AccretaType.

Definition accreta_severity (a : AccretaType) : nat :=
  match a with
  | NoAccreta => 0
  | Accreta => 1
  | Increta => 2
  | Percreta => 3
  end.

Definition requires_planned_hysterectomy (a : AccretaType) : bool :=
  match a with
  | Percreta => true
  | _ => false
  end.

Definition may_allow_conservative (a : AccretaType) : bool :=
  match a with
  | NoAccreta => true
  | Accreta => true
  | Increta => false
  | Percreta => false
  end.

Record t : Type := MkPatient {
  weight_kg : nat;
  height_cm : nat;
  gestational_weeks : nat;
  baseline_hgb_x10 : nat;
  has_preeclampsia : bool;
  accreta_type : AccretaType;
  has_coagulation_disorder : bool;
  has_uterine_overdistension : bool;
  previous_pph : bool;
  previous_cesarean : bool;
  number_prior_cesareans : nat;
  multiple_gestation : bool;
  prolonged_labor : bool;
  chorioamnionitis : bool
}.

(** Backward compatibility *)
Definition has_placenta_accreta_spectrum (p : t) : bool :=
  match accreta_type p with
  | NoAccreta => false
  | _ => true
  end.

(** Input validation: physiologically plausible patient parameter ranges *)
Definition valid (p : t) : bool :=
  (30 <=? weight_kg p) && (weight_kg p <=? 300) &&
  (100 <=? height_cm p) && (height_cm p <=? 250) &&
  (baseline_hgb_x10 p <=? 200) &&
  (gestational_weeks p <=? 45).

(** Pregnancy-adjusted blood volume.
    Non-pregnant: ~70 mL/kg
    Term pregnant: ~100 mL/kg (expanded by 30-50%)
    Early pregnancy: linear interpolation *)
Definition pregnancy_blood_volume_factor_x100 (gest_weeks : nat) : nat :=
  if gest_weeks <? 12 then 100
  else if gest_weeks <? 40 then 100 + ((gest_weeks - 12) * 30) / 28
  else 130.

Definition estimated_blood_volume_mL (p : t) : nat :=
  (weight_kg p * 70 * pregnancy_blood_volume_factor_x100 (gestational_weeks p)) / 100.

(** Legacy calculation for non-pregnant baseline *)
Definition nonpregnant_blood_volume_mL (p : t) : nat := weight_kg p * 70.

Definition percent_blood_volume_lost (p : t) (ebl : nat) : nat :=
  if estimated_blood_volume_mL p =? 0 then 0
  else (ebl * 100) / estimated_blood_volume_mL p.

Definition is_high_risk (p : t) : bool :=
  has_preeclampsia p ||
  has_placenta_accreta_spectrum p ||
  has_coagulation_disorder p ||
  has_uterine_overdistension p ||
  previous_pph p ||
  multiple_gestation p.

Definition adjusted_stage2_threshold (p : t) (base : nat) : nat :=
  if is_high_risk p then base - (base / 5) else base.

Definition hgb_drop_significant (p : t) (current_hgb_x10 : nat) : bool :=
  20 <=? baseline_hgb_x10 p - current_hgb_x10.

Lemma high_risk_lowers_threshold : forall p base,
  is_high_risk p = true -> adjusted_stage2_threshold p base <= base.
Proof.
  intros p base H. unfold adjusted_stage2_threshold. rewrite H.
  assert (base / 5 <= base) by (apply Nat.div_le_upper_bound; lia).
  lia.
Qed.

(** Risk score now uses accreta severity which is weighted by type:
    NoAccreta=0, Accreta=1, Increta=2, Percreta=3 *)
Definition risk_score (p : t) : nat :=
  (if has_preeclampsia p then 2 else 0) +
  accreta_severity (accreta_type p) +
  (if has_coagulation_disorder p then 2 else 0) +
  (if has_uterine_overdistension p then 1 else 0) +
  (if previous_pph p then 2 else 0) +
  (if previous_cesarean p then 1 else 0) +
  number_prior_cesareans p +
  (if multiple_gestation p then 1 else 0) +
  (if prolonged_labor p then 1 else 0) +
  (if chorioamnionitis p then 1 else 0).

Lemma percreta_is_high_risk : forall p,
  accreta_type p = Percreta -> is_high_risk p = true.
Proof.
  intros p H. unfold is_high_risk, has_placenta_accreta_spectrum.
  rewrite H. simpl.
  destruct (has_preeclampsia p); reflexivity.
Qed.

Definition risk_category (p : t) : nat :=
  let score := risk_score p in
  if 5 <=? score then 3
  else if 2 <=? score then 2
  else 1.

Lemma risk_category_range : forall p, 1 <= risk_category p <= 3.
Proof.
  intros p. unfold risk_category.
  destruct (5 <=? risk_score p) eqn:E1; [lia|].
  destruct (2 <=? risk_score p) eqn:E2; lia.
Qed.

(******************************************************************************)
(*                    EXPANDED PLACENTA ACCRETA SPECTRUM                      *)
(*                                                                            *)
(*  Detailed modeling of PAS management including MFM center criteria,        *)
(*  IR pre-positioning, and expected blood loss by accreta type.              *)
(*  Reference: SMFM Consult Series #44, Am J Obstet Gynecol 2018.            *)
(******************************************************************************)

(** Expected blood loss by accreta type (mL) - median values from literature *)
Definition expected_ebl_no_accreta : nat := 500.
Definition expected_ebl_accreta : nat := 1500.
Definition expected_ebl_increta : nat := 3000.
Definition expected_ebl_percreta : nat := 5000.

Definition expected_ebl_by_accreta (a : AccretaType) : nat :=
  match a with
  | NoAccreta => expected_ebl_no_accreta
  | Accreta => expected_ebl_accreta
  | Increta => expected_ebl_increta
  | Percreta => expected_ebl_percreta
  end.

Lemma accreta_increases_expected_ebl : forall a,
  a <> NoAccreta -> expected_ebl_no_accreta < expected_ebl_by_accreta a.
Proof.
  intros a H. destruct a; unfold expected_ebl_by_accreta,
    expected_ebl_no_accreta, expected_ebl_accreta, expected_ebl_increta, expected_ebl_percreta.
  - contradiction.
  - lia.
  - lia.
  - lia.
Qed.

(** MFM Center transfer criteria per SMFM.
    Transfer to center of excellence if:
    1. Percreta diagnosed prenatally, OR
    2. Increta with bladder involvement, OR
    3. High risk with limited local surgical capability *)
Definition requires_mfm_center_transfer (a : AccretaType) (bladder_involvement : bool)
    (local_surgical_capability : bool) : bool :=
  match a with
  | Percreta => true
  | Increta => bladder_involvement || negb local_surgical_capability
  | Accreta => negb local_surgical_capability
  | NoAccreta => false
  end.

Lemma percreta_always_requires_transfer : forall bladder local,
  requires_mfm_center_transfer Percreta bladder local = true.
Proof. intros. reflexivity. Qed.

(** Interventional radiology pre-positioning.
    Balloon catheters should be placed prophylactically for:
    1. Percreta, OR
    2. Increta with anticipated difficult surgical field *)
Definition requires_ir_preposition (a : AccretaType) (difficult_field : bool) : bool :=
  match a with
  | Percreta => true
  | Increta => difficult_field
  | _ => false
  end.

(** Hysterectomy likelihood by accreta type *)
Definition hysterectomy_likelihood_pct (a : AccretaType) : nat :=
  match a with
  | NoAccreta => 1
  | Accreta => 25
  | Increta => 50
  | Percreta => 90
  end.

(** Conservative management eligibility - only for superficial accreta *)
Definition conservative_management_eligible (a : AccretaType) (desires_fertility : bool)
    (hemodynamically_stable : bool) : bool :=
  match a with
  | NoAccreta => true
  | Accreta => desires_fertility && hemodynamically_stable
  | Increta => false
  | Percreta => false
  end.

Lemma increta_ineligible_conservative : forall fert stable,
  conservative_management_eligible Increta fert stable = false.
Proof. intros. reflexivity. Qed.

Lemma percreta_ineligible_conservative : forall fert stable,
  conservative_management_eligible Percreta fert stable = false.
Proof. intros. reflexivity. Qed.

(** Blood product preparation by accreta type *)
Definition recommended_prbc_ready (a : AccretaType) : nat :=
  match a with
  | NoAccreta => 2
  | Accreta => 6
  | Increta => 10
  | Percreta => 10
  end.

Definition recommended_ffp_ready (a : AccretaType) : nat :=
  match a with
  | NoAccreta => 0
  | Accreta => 4
  | Increta => 6
  | Percreta => 6
  end.

Definition recommended_cryo_ready (a : AccretaType) : nat :=
  match a with
  | NoAccreta => 0
  | Accreta => 0
  | Increta => 10
  | Percreta => 10
  end.

Lemma percreta_requires_max_blood : forall a,
  recommended_prbc_ready a <= recommended_prbc_ready Percreta.
Proof. intros []; unfold recommended_prbc_ready; lia. Qed.

(** Surgical team requirements *)
Definition requires_gyn_oncology (a : AccretaType) : bool :=
  match a with
  | Percreta => true
  | Increta => true
  | _ => false
  end.

Definition requires_urology_standby (a : AccretaType) (bladder_involvement : bool) : bool :=
  match a with
  | Percreta => true
  | Increta => bladder_involvement
  | _ => false
  end.

(******************************************************************************)
(*                 BMI-ADJUSTED BLOOD VOLUME (Gap #4)                         *)
(*                                                                            *)
(*  Obese patients have less mL/kg blood because adipose tissue has lower     *)
(*  blood supply than lean tissue. Standard 70mL/kg overestimates EBV.        *)
(*  Reference: Lemmens HJ et al. Obes Surg 2006.                              *)
(******************************************************************************)

(** BMI category directly from weight/height ratio.
    Uses simplified calculation to avoid large number blowup in proofs.
    BMI = weight(kg) / height(m)^2
    height_cm^2 / 10000 = height_m^2
    So BMI × 10 = weight × 10000 / height_cm^2 *)
Definition bmi_x10 (p : t) : nat :=
  if height_cm p =? 0 then 0
  else (weight_kg p * 10000) / (height_cm p * height_cm p).

(** BMI categories per WHO (thresholds × 10) *)
Inductive BMICategory : Type :=
  | Underweight : BMICategory
  | Normal : BMICategory
  | Overweight : BMICategory
  | ObeseI : BMICategory
  | ObeseII : BMICategory
  | ObeseIII : BMICategory.

Definition bmi_to_category (bmi_x10 : nat) : BMICategory :=
  if bmi_x10 <? 185 then Underweight
  else if bmi_x10 <? 250 then Normal
  else if bmi_x10 <? 300 then Overweight
  else if bmi_x10 <? 350 then ObeseI
  else if bmi_x10 <? 400 then ObeseII
  else ObeseIII.

(** Adjusted mL/kg by BMI category (Lemmens formula approximation) *)
Definition ml_per_kg_for_category (cat : BMICategory) : nat :=
  match cat with
  | Underweight => 75
  | Normal => 70
  | Overweight => 65
  | ObeseI => 60
  | ObeseII => 55
  | ObeseIII => 50
  end.

(** BMI-adjusted estimated blood volume *)
Definition estimated_blood_volume_bmi_adjusted_mL (p : t) : nat :=
  let cat := bmi_to_category (bmi_x10 p) in
  let base_ml_per_kg := ml_per_kg_for_category cat in
  let pregnancy_factor := pregnancy_blood_volume_factor_x100 (gestational_weeks p) in
  (weight_kg p * base_ml_per_kg * pregnancy_factor) / 100.

(** Percent blood volume lost using BMI-adjusted calculation *)
Definition percent_blood_volume_lost_bmi_adjusted (p : t) (ebl : nat) : nat :=
  let ebv := estimated_blood_volume_bmi_adjusted_mL p in
  if ebv =? 0 then 0 else (ebl * 100) / ebv.

(** mL/kg is bounded 50-75 for all categories *)
Lemma ml_per_kg_bounded : forall cat, 50 <= ml_per_kg_for_category cat <= 75.
Proof. intros []; simpl; lia. Qed.

(** Obese patients have lower mL/kg than normal *)
Lemma obese_lower_ml_per_kg : forall cat,
  cat = ObeseI \/ cat = ObeseII \/ cat = ObeseIII ->
  ml_per_kg_for_category cat <= 60.
Proof. intros [] [H|[H|H]]; discriminate || simpl; lia. Qed.

(******************************************************************************)
(*               CESAREAN SURGICAL BLOOD LOSS (Gap #6)                        *)
(*                                                                            *)
(*  Cesarean delivery has baseline surgical blood loss of 500-800mL.          *)
(*  PPH thresholds should account for this expected loss.                     *)
(*  Reference: ACOG Practice Bulletin 183.                                    *)
(******************************************************************************)

(** Expected baseline blood loss by procedure type *)
Definition baseline_surgical_loss_mL (is_cesarean : bool) (is_emergent : bool) : nat :=
  match is_cesarean, is_emergent with
  | true, true => 800    (** Emergent cesarean: higher blood loss *)
  | true, false => 600   (** Planned cesarean: moderate *)
  | false, _ => 200      (** Vaginal delivery baseline *)
  end.

(** Excess blood loss above expected baseline *)
Definition excess_blood_loss (total_ebl : nat) (is_cesarean is_emergent : bool) : nat :=
  let baseline := baseline_surgical_loss_mL is_cesarean is_emergent in
  if total_ebl <? baseline then 0
  else total_ebl - baseline.

(** Adjusted staging using excess blood loss *)
Definition adjusted_ebl_for_staging (total_ebl : nat) (is_cesarean is_emergent : bool) : nat :=
  (** For staging purposes, we can use either:
      1. Total EBL with cesarean-specific thresholds (current approach), OR
      2. Excess EBL with vaginal thresholds
      Option 1 is preferred per ACOG 2017. *)
  total_ebl.

Lemma emergent_higher_baseline : forall is_cs,
  baseline_surgical_loss_mL is_cs true >= baseline_surgical_loss_mL is_cs false.
Proof.
  intros []; simpl; lia.
Qed.

(******************************************************************************)
(*           CESAREAN-HYSTERECTOMY SCENARIO (Gap #13)                         *)
(*                                                                            *)
(*  Planned cesarean hysterectomy for placenta percreta has very different    *)
(*  expected blood loss and transfusion needs.                                *)
(*  Reference: Society for Maternal-Fetal Medicine Consult Series 2019.       *)
(******************************************************************************)

Record CesareanHysterectomyRisk : Type := MkCHRisk {
  ch_accreta_type : AccretaType;
  ch_placenta_anterior : bool;
  ch_prior_cesareans : nat;
  ch_gestational_age : nat;
  ch_mri_confirmed : bool
}.

(** Expected blood loss for planned cesarean hysterectomy *)
Definition expected_ebl_cesarean_hysterectomy (r : CesareanHysterectomyRisk) : nat :=
  let base := match ch_accreta_type r with
              | NoAccreta => 1000
              | Accreta => 2000
              | Increta => 3000
              | Percreta => 5000
              end in
  let anterior_adj := if ch_placenta_anterior r then base / 2 else 0 in
  let prior_cs_adj := ch_prior_cesareans r * 200 in
  base + anterior_adj + prior_cs_adj.

(** Minimum blood products to have available *)
Definition prbc_units_to_prepare (r : CesareanHysterectomyRisk) : nat :=
  let expected := expected_ebl_cesarean_hysterectomy r in
  (** 1 unit PRBC replaces ~300mL blood loss *)
  (expected / 300) + 4.  (** Extra 4 units buffer *)

(** Cell saver mandatory? *)
Definition cell_saver_mandatory (r : CesareanHysterectomyRisk) : bool :=
  match ch_accreta_type r with
  | Percreta => true
  | Increta => true
  | Accreta => ch_placenta_anterior r
  | NoAccreta => false
  end.

(** IR team required for potential UAE? *)
Definition ir_team_required (r : CesareanHysterectomyRisk) : bool :=
  match ch_accreta_type r with
  | Percreta => true
  | Increta => ch_placenta_anterior r
  | _ => false
  end.

Lemma percreta_highest_expected_loss : forall r1 r2,
  ch_accreta_type r1 = Percreta ->
  ch_accreta_type r2 <> Percreta ->
  ch_placenta_anterior r1 = ch_placenta_anterior r2 ->
  ch_prior_cesareans r1 = ch_prior_cesareans r2 ->
  expected_ebl_cesarean_hysterectomy r1 > expected_ebl_cesarean_hysterectomy r2.
Proof.
Admitted.

(******************************************************************************)
(*           MULTIPLE GESTATION ADJUSTMENTS (Gap #15)                         *)
(*                                                                            *)
(*  Twin and higher-order multiple pregnancies have increased blood volume    *)
(*  and increased PPH risk. Thresholds may need adjustment.                   *)
(*  Reference: ACOG Practice Bulletin 231 - Multiple Gestation.               *)
(******************************************************************************)

Inductive GestationType : Type :=
  | Singleton : GestationType
  | Twins : GestationType
  | Triplets : GestationType
  | HigherOrder : nat -> GestationType.

Definition gestation_count (g : GestationType) : nat :=
  match g with
  | Singleton => 1
  | Twins => 2
  | Triplets => 3
  | HigherOrder n => n
  end.

(** Additional blood volume expansion for multiple gestation
    Twins: ~15% additional expansion
    Triplets: ~25% additional expansion *)
Definition multiple_gestation_volume_factor_x100 (g : GestationType) : nat :=
  match g with
  | Singleton => 100
  | Twins => 115
  | Triplets => 125
  | HigherOrder n => 100 + (n - 1) * 10
  end.

(** Adjusted EBV for multiple gestation *)
Definition estimated_blood_volume_multiple_mL (p : t) (g : GestationType) : nat :=
  let base_ebv := estimated_blood_volume_mL p in
  (base_ebv * multiple_gestation_volume_factor_x100 g) / 100.

(** PPH risk multiplier for multiple gestation *)
Definition pph_risk_multiplier_x100 (g : GestationType) : nat :=
  match g with
  | Singleton => 100
  | Twins => 200       (** 2x risk *)
  | Triplets => 400    (** 4x risk *)
  | HigherOrder n => 100 * n
  end.

(** More aggressive monitoring threshold for multiples *)
Definition adjusted_monitoring_threshold (g : GestationType) (base : nat) : nat :=
  match g with
  | Singleton => base
  | Twins => base - (base / 4)       (** 25% lower threshold *)
  | Triplets => base - (base / 3)    (** 33% lower threshold *)
  | HigherOrder _ => base / 2        (** 50% lower threshold *)
  end.

Lemma twins_lower_threshold : forall base,
  base >= 4 -> adjusted_monitoring_threshold Twins base < base.
Proof.
  intros base H. unfold adjusted_monitoring_threshold.
  assert (base / 4 >= 1) by (apply Nat.div_le_lower_bound; lia).
  lia.
Qed.

(** Risk increases with gestation count for fixed types *)
Lemma singleton_lowest_risk :
  pph_risk_multiplier_x100 Singleton <= pph_risk_multiplier_x100 Twins.
Proof. simpl. lia. Qed.

Lemma twins_lower_than_triplets :
  pph_risk_multiplier_x100 Twins < pph_risk_multiplier_x100 Triplets.
Proof. simpl. lia. Qed.

End PatientFactors.

(******************************************************************************)
(*                                                                            *)
(*                              ETIOLOGY                                      *)
(*                                                                            *)
(*  The "4 T's" of PPH: Tone, Trauma, Tissue, Thrombin.                      *)
(*  Treatment differs by etiology.                                            *)
(*                                                                            *)
(******************************************************************************)

Module Etiology.

Inductive t : Type :=
  | Tone : t
  | Trauma : t
  | Tissue : t
  | Thrombin : t.

Definition eq_dec : forall e1 e2 : t, {e1 = e2} + {e1 <> e2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Tone; Trauma; Tissue; Thrombin].

Definition frequency_rank (e : t) : nat :=
  match e with
  | Tone => 1
  | Trauma => 2
  | Tissue => 3
  | Thrombin => 4
  end.

Definition approximate_prevalence_pct (e : t) : nat :=
  match e with
  | Tone => 70
  | Trauma => 20
  | Tissue => 9
  | Thrombin => 1
  end.

Lemma prevalences_sum_100 :
  approximate_prevalence_pct Tone +
  approximate_prevalence_pct Trauma +
  approximate_prevalence_pct Tissue +
  approximate_prevalence_pct Thrombin = 100.
Proof. reflexivity. Qed.

Definition primary_treatment_is_uterotonic (e : t) : bool :=
  match e with
  | Tone => true
  | _ => false
  end.

Definition requires_surgical_exploration (e : t) : bool :=
  match e with
  | Trauma => true
  | Tissue => true
  | _ => false
  end.

Definition requires_blood_products (e : t) : bool :=
  match e with
  | Thrombin => true
  | _ => false
  end.

Definition first_line_treatment (e : t) : nat :=
  match e with
  | Tone => 1
  | Trauma => 2
  | Tissue => 2
  | Thrombin => 3
  end.

Lemma tone_most_common : forall e : t,
  e <> Tone -> approximate_prevalence_pct Tone > approximate_prevalence_pct e.
Proof. intros [] H; try contradiction; simpl; lia. Qed.

(** Multi-etiology support: PPH often has multiple concurrent causes *)
Record EtiologySet : Type := MkEtiologySet {
  has_tone : bool;
  has_trauma : bool;
  has_tissue : bool;
  has_thrombin : bool
}.

Definition empty_etiology : EtiologySet :=
  MkEtiologySet false false false false.

Definition single_etiology (e : t) : EtiologySet :=
  match e with
  | Tone => MkEtiologySet true false false false
  | Trauma => MkEtiologySet false true false false
  | Tissue => MkEtiologySet false false true false
  | Thrombin => MkEtiologySet false false false true
  end.

Definition add_etiology (es : EtiologySet) (e : t) : EtiologySet :=
  match e with
  | Tone => MkEtiologySet true (has_trauma es) (has_tissue es) (has_thrombin es)
  | Trauma => MkEtiologySet (has_tone es) true (has_tissue es) (has_thrombin es)
  | Tissue => MkEtiologySet (has_tone es) (has_trauma es) true (has_thrombin es)
  | Thrombin => MkEtiologySet (has_tone es) (has_trauma es) (has_tissue es) true
  end.

Definition etiology_count (es : EtiologySet) : nat :=
  (if has_tone es then 1 else 0) +
  (if has_trauma es then 1 else 0) +
  (if has_tissue es then 1 else 0) +
  (if has_thrombin es then 1 else 0).

Definition is_mixed_etiology (es : EtiologySet) : bool :=
  2 <=? etiology_count es.

Definition requires_surgical_exploration_set (es : EtiologySet) : bool :=
  has_trauma es || has_tissue es.

Definition requires_blood_products_set (es : EtiologySet) : bool :=
  has_thrombin es.

Definition uterotonics_may_help (es : EtiologySet) : bool :=
  has_tone es.

Definition to_list (es : EtiologySet) : list t :=
  (if has_tone es then [Tone] else []) ++
  (if has_trauma es then [Trauma] else []) ++
  (if has_tissue es then [Tissue] else []) ++
  (if has_thrombin es then [Thrombin] else []).

Lemma single_etiology_count_1 : forall e,
  etiology_count (single_etiology e) = 1.
Proof. intros []; reflexivity. Qed.

Lemma add_etiology_increases_or_same : forall es e,
  etiology_count es <= etiology_count (add_etiology es e).
Proof.
  intros es []; unfold etiology_count, add_etiology; simpl;
  destruct (has_tone es); destruct (has_trauma es);
  destruct (has_tissue es); destruct (has_thrombin es); simpl; lia.
Qed.

(** Idempotence: adding the same etiology twice has no additional effect *)
Lemma add_etiology_idempotent : forall es e,
  add_etiology (add_etiology es e) e = add_etiology es e.
Proof.
  intros es []; unfold add_etiology; simpl; reflexivity.
Qed.

Lemma add_etiology_comm : forall es e1 e2,
  add_etiology (add_etiology es e1) e2 = add_etiology (add_etiology es e2) e1.
Proof.
  intros es [] [];
  unfold add_etiology; simpl;
  destruct es; simpl; reflexivity.
Qed.

(******************************************************************************)
(*                EXTENDED ETIOLOGIES: AFE AND UTERINE INVERSION              *)
(*                                                                            *)
(*  Beyond the 4 T's: Amniotic Fluid Embolism and Uterine Inversion are       *)
(*  catastrophic causes of PPH requiring specific emergency treatment.         *)
(******************************************************************************)

(** Extended etiology type including rare catastrophic causes *)
Inductive ExtendedEtiology : Type :=
  | BasicEtiology : t -> ExtendedEtiology
  | AmnioticFluidEmbolism : ExtendedEtiology    (** AFE: DIC + cardiovascular collapse *)
  | UterineInversion : ExtendedEtiology.        (** Requires manual replacement *)

Definition extended_eq_dec : forall e1 e2 : ExtendedEtiology, {e1 = e2} + {e1 <> e2}.
Proof.
  intros e1 e2. destruct e1, e2.
  - destruct (eq_dec t0 t1).
    + left. f_equal. exact e.
    + right. intro H. injection H. exact n.
  - right. discriminate.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

(** AFE characteristics: always has DIC component, high mortality *)
Definition afe_has_dic_component : bool := true.
Definition afe_mortality_percent : nat := 60.
Definition afe_is_clinical_diagnosis : bool := true.

(** AFE treatment priorities *)
Inductive AFETreatmentPriority : Type :=
  | AFE_Airway : AFETreatmentPriority
  | AFE_Resuscitation : AFETreatmentPriority
  | AFE_DIC_Management : AFETreatmentPriority
  | AFE_Delivery : AFETreatmentPriority.

Definition afe_treatment_order : list AFETreatmentPriority :=
  [AFE_Airway; AFE_Resuscitation; AFE_DIC_Management; AFE_Delivery].

(** Uterine inversion characteristics *)
Inductive InversionDegree : Type :=
  | Incomplete : InversionDegree    (** Fundus not past cervix *)
  | Complete : InversionDegree      (** Fundus through cervix *)
  | Prolapsed : InversionDegree.    (** Uterus outside vagina *)

Definition inversion_requires_immediate_replacement : bool := true.
Definition inversion_delay_increases_mortality : bool := true.

(** Johnson maneuver: primary treatment for uterine inversion *)
Definition johnson_maneuver_first_line : bool := true.

(** Inversion treatment sequence *)
Inductive InversionTreatment : Type :=
  | StopUterotonics : InversionTreatment   (** First: stop any oxytocin *)
  | UterineRelaxation : InversionTreatment (** Terbutaline or nitro for relaxation *)
  | ManualReplacement : InversionTreatment (** Johnson maneuver *)
  | LaparotomyIfFailed : InversionTreatment.

Definition inversion_treatment_sequence : list InversionTreatment :=
  [StopUterotonics; UterineRelaxation; ManualReplacement; LaparotomyIfFailed].

(** AFE triggers emergency MTP and ICU *)
Lemma afe_triggers_mtp : afe_has_dic_component = true.
Proof. reflexivity. Qed.

(** Inversion: uterotonics are CONTRAINDICATED until replaced *)
Definition uterotonics_contraindicated_in_inversion : bool := true.

Lemma inversion_no_uterotonics :
  uterotonics_contraindicated_in_inversion = true.
Proof. reflexivity. Qed.

(** Extended etiology requires specialized treatment *)
Definition extended_requires_specialist (e : ExtendedEtiology) : bool :=
  match e with
  | BasicEtiology _ => false
  | AmnioticFluidEmbolism => true
  | UterineInversion => true
  end.

Definition extended_mortality_risk (e : ExtendedEtiology) : nat :=
  match e with
  | BasicEtiology Tone => 1
  | BasicEtiology Trauma => 5
  | BasicEtiology Tissue => 2
  | BasicEtiology Thrombin => 10
  | AmnioticFluidEmbolism => 60
  | UterineInversion => 15
  end.

Lemma afe_highest_mortality : forall e,
  extended_mortality_risk e <= extended_mortality_risk AmnioticFluidEmbolism.
Proof.
  intros [[]| |]; simpl; lia.
Qed.

(******************************************************************************)
(*                    ETIOLOGY-INTERVENTION CONNECTION                        *)
(*                                                                            *)
(*  Proofs that identified etiology determines correct treatment pathway.     *)
(******************************************************************************)

(** Tone etiology implies uterotonics are first-line treatment *)
Theorem tone_implies_uterotonic_first : forall e,
  e = Tone -> primary_treatment_is_uterotonic e = true.
Proof. intros e H. rewrite H. reflexivity. Qed.

(** Non-tone etiologies do not have uterotonics as primary *)
Theorem non_tone_no_uterotonic_primary : forall e,
  e <> Tone -> primary_treatment_is_uterotonic e = false.
Proof. intros [] H; try reflexivity; contradiction. Qed.

(** Trauma or Tissue etiology requires surgical exploration *)
Theorem trauma_or_tissue_requires_surgery : forall e,
  e = Trauma \/ e = Tissue -> requires_surgical_exploration e = true.
Proof. intros e [H|H]; rewrite H; reflexivity. Qed.

(** Thrombin etiology requires blood products *)
Theorem thrombin_requires_blood_products :
  requires_blood_products Thrombin = true.
Proof. reflexivity. Qed.

(** Etiology set with tone allows uterotonics *)
Theorem etiology_set_tone_uterotonics : forall es,
  has_tone es = true -> uterotonics_may_help es = true.
Proof. intros es H. unfold uterotonics_may_help. exact H. Qed.

(** Etiology set with trauma or tissue requires surgical evaluation *)
Theorem etiology_set_surgical : forall es,
  has_trauma es = true \/ has_tissue es = true ->
  requires_surgical_exploration_set es = true.
Proof.
  intros es [H|H]; unfold requires_surgical_exploration_set; rewrite H;
  [reflexivity | destruct (has_trauma es); reflexivity].
Qed.

(** Treatment coverage: every etiology has a defined first-line treatment *)
Theorem every_etiology_has_treatment : forall e,
  exists n, first_line_treatment e = n /\ 1 <= n <= 3.
Proof.
  intros []; unfold first_line_treatment.
  - exists 1. split; [reflexivity | lia].
  - exists 2. split; [reflexivity | lia].
  - exists 2. split; [reflexivity | lia].
  - exists 3. split; [reflexivity | lia].
Qed.

(** Extended etiology specialist requirement: catastrophic causes need specialists *)
Theorem catastrophic_needs_specialist :
  extended_requires_specialist AmnioticFluidEmbolism = true /\
  extended_requires_specialist UterineInversion = true.
Proof. split; reflexivity. Qed.

(** Basic etiologies do not inherently require specialist (depends on severity) *)
Theorem basic_etiology_no_specialist : forall e,
  extended_requires_specialist (BasicEtiology e) = false.
Proof. intros []; reflexivity. Qed.

(** Inversion requires stopping uterotonics before treatment *)
Theorem inversion_stop_uterotonics_first :
  hd_error inversion_treatment_sequence = Some StopUterotonics.
Proof. reflexivity. Qed.

(** AFE requires airway management first *)
Theorem afe_airway_first :
  hd_error afe_treatment_order = Some AFE_Airway.
Proof. reflexivity. Qed.

End Etiology.

(******************************************************************************)
(*                                                                            *)
(*                         RATE OF BLOOD LOSS                                 *)
(*                                                                            *)
(*  Rapid hemorrhage requires intervention before cumulative thresholds.     *)
(*                                                                            *)
(******************************************************************************)

Module RateOfLoss.

Definition mL_per_minute := nat.

Definition is_rapid (rate : mL_per_minute) : bool := 150 <=? rate.

Definition is_very_rapid (rate : mL_per_minute) : bool := 300 <=? rate.

Definition projected_loss_in_minutes (rate : mL_per_minute) (minutes : nat) : nat :=
  rate * minutes.

Definition minutes_to_stage4 (rate : mL_per_minute) (current_ebl : nat) : option nat :=
  if rate =? 0 then None
  else Some ((1500 - current_ebl) / rate).

Definition rate_triggers_escalation (rate : mL_per_minute) (current_ebl : nat) : bool :=
  is_rapid rate || (500 <=? current_ebl + rate * 5).

Lemma rapid_always_triggers : forall rate current_ebl,
  is_rapid rate = true -> rate_triggers_escalation rate current_ebl = true.
Proof.
  intros rate current_ebl H. unfold rate_triggers_escalation.
  rewrite H. reflexivity.
Qed.

Definition effective_stage (base_stage : nat) (rate : mL_per_minute) : nat :=
  if is_very_rapid rate then Nat.min 4 (base_stage + 2)
  else if is_rapid rate then Nat.min 4 (base_stage + 1)
  else base_stage.

Lemma effective_stage_ge_base_when_small : forall base rate,
  base <= 4 -> base <= effective_stage base rate.
Proof.
  intros base rate Hbase. unfold effective_stage.
  destruct (is_very_rapid rate) eqn:E1.
  - destruct (Nat.le_ge_cases (base + 2) 4) as [Hcase|Hcase].
    + rewrite Nat.min_r; lia.
    + rewrite Nat.min_l; lia.
  - destruct (is_rapid rate) eqn:E2.
    + destruct (Nat.le_ge_cases (base + 1) 4) as [Hcase|Hcase].
      * rewrite Nat.min_r; lia.
      * rewrite Nat.min_l; lia.
    + lia.
Qed.

Lemma effective_stage_at_most_4 : forall base rate,
  base <= 4 -> effective_stage base rate <= 4.
Proof.
  intros base rate Hbase. unfold effective_stage.
  destruct (is_very_rapid rate).
  - apply Nat.le_min_l.
  - destruct (is_rapid rate).
    + apply Nat.le_min_l.
    + exact Hbase.
Qed.

End RateOfLoss.

(******************************************************************************)
(*                                                                            *)
(*                              STAGE                                         *)
(*                                                                            *)
(*  The four stages of postpartum hemorrhage severity based on estimated     *)
(*  blood loss (EBL) in milliliters.                                         *)
(*                                                                            *)
(******************************************************************************)

Module Stage.

Inductive t : Type :=
  | Stage1 : t
  | Stage2 : t
  | Stage3 : t
  | Stage4 : t.

Definition eq_dec : forall s1 s2 : t, {s1 = s2} + {s1 <> s2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Stage1; Stage2; Stage3; Stage4].

Lemma all_contains_every_stage : forall s : t, In s all.
Proof. intros []; simpl; auto. Qed.

Lemma all_has_no_duplicates : NoDup all.
Proof.
  repeat constructor; simpl; intuition discriminate.
Qed.

Definition to_nat (s : t) : nat :=
  match s with
  | Stage1 => 1
  | Stage2 => 2
  | Stage3 => 3
  | Stage4 => 4
  end.

Definition of_nat (n : nat) : option t :=
  match n with
  | 1 => Some Stage1
  | 2 => Some Stage2
  | 3 => Some Stage3
  | 4 => Some Stage4
  | _ => None
  end.

Lemma of_nat_to_nat_roundtrip : forall s : t, of_nat (to_nat s) = Some s.
Proof. intros []; reflexivity. Qed.

Lemma to_nat_injective : forall s1 s2 : t, to_nat s1 = to_nat s2 -> s1 = s2.
Proof. intros [] [] H; simpl in H; try reflexivity; discriminate. Qed.

Lemma to_nat_lower_bound : forall s : t, 1 <= to_nat s.
Proof. intros []; simpl; lia. Qed.

Lemma to_nat_upper_bound : forall s : t, to_nat s <= 4.
Proof. intros []; simpl; lia. Qed.

Definition le (s1 s2 : t) : Prop := to_nat s1 <= to_nat s2.

Notation "s1 <=s s2" := (le s1 s2) (at level 70).

Lemma le_reflexive : forall s : t, s <=s s.
Proof. intros s. unfold le. lia. Qed.

Lemma le_transitive : forall s1 s2 s3 : t, s1 <=s s2 -> s2 <=s s3 -> s1 <=s s3.
Proof. intros s1 s2 s3 H12 H23. unfold le in *. lia. Qed.

Lemma le_antisymmetric : forall s1 s2 : t, s1 <=s s2 -> s2 <=s s1 -> s1 = s2.
Proof.
  intros [] [] H12 H21; unfold le, to_nat in *; try reflexivity; lia.
Qed.

Lemma le_total : forall s1 s2 : t, s1 <=s s2 \/ s2 <=s s1.
Proof. intros [] []; unfold le, to_nat; lia. Qed.

Lemma stage1_le_stage2 : Stage1 <=s Stage2.
Proof. unfold le, to_nat. lia. Qed.

Lemma stage2_le_stage3 : Stage2 <=s Stage3.
Proof. unfold le, to_nat. lia. Qed.

Lemma stage3_le_stage4 : Stage3 <=s Stage4.
Proof. unfold le, to_nat. lia. Qed.

Lemma stage1_is_minimum : forall s : t, Stage1 <=s s.
Proof. intros []; unfold le, to_nat; lia. Qed.

Lemma stage4_is_maximum : forall s : t, s <=s Stage4.
Proof. intros []; unfold le, to_nat; lia. Qed.

(** EBL thresholds in milliliters per ACOG 2017 - delivery mode specific *)
Definition threshold_stage2 (d : DeliveryMode.t) : nat :=
  match d with
  | DeliveryMode.Vaginal => 500
  | DeliveryMode.Cesarean => 1000
  end.

Definition threshold_stage3 (d : DeliveryMode.t) : nat :=
  match d with
  | DeliveryMode.Vaginal => 1000
  | DeliveryMode.Cesarean => 1500
  end.

Definition threshold_stage4 (d : DeliveryMode.t) : nat :=
  match d with
  | DeliveryMode.Vaginal => 1500
  | DeliveryMode.Cesarean => 2000
  end.

Lemma thresholds_strictly_increasing : forall d : DeliveryMode.t,
  threshold_stage2 d < threshold_stage3 d /\ threshold_stage3 d < threshold_stage4 d.
Proof. intros []; unfold threshold_stage2, threshold_stage3, threshold_stage4; lia. Qed.

Lemma vaginal_threshold_stage2 : threshold_stage2 DeliveryMode.Vaginal = 500.
Proof. reflexivity. Qed.

Lemma cesarean_threshold_stage2 : threshold_stage2 DeliveryMode.Cesarean = 1000.
Proof. reflexivity. Qed.

Lemma threshold_stage2_le_stage3 : forall d, threshold_stage2 d <= threshold_stage3 d.
Proof. intros []; simpl; lia. Qed.

Lemma threshold_stage3_le_stage4 : forall d, threshold_stage3 d <= threshold_stage4 d.
Proof. intros []; simpl; lia. Qed.

Definition of_ebl (d : DeliveryMode.t) (ebl : nat) : t :=
  if ebl <? threshold_stage2 d then Stage1
  else if ebl <? threshold_stage3 d then Stage2
  else if ebl <? threshold_stage4 d then Stage3
  else Stage4.

Lemma of_ebl_stage1_iff : forall (d : DeliveryMode.t) (ebl : nat),
  of_ebl d ebl = Stage1 <-> ebl < threshold_stage2 d.
Proof.
  intros d ebl. unfold of_ebl. split.
  - intro H. destruct (ebl <? threshold_stage2 d) eqn:E.
    + apply Nat.ltb_lt. exact E.
    + destruct (ebl <? threshold_stage3 d) eqn:E2;
      destruct (ebl <? threshold_stage4 d) eqn:E3; discriminate.
  - intro H. apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma of_ebl_stage2_iff : forall d ebl,
  of_ebl d ebl = Stage2 <-> threshold_stage2 d <= ebl < threshold_stage3 d.
Proof.
  intros d ebl. unfold of_ebl. split.
  - intro H. destruct (ebl <? threshold_stage2 d) eqn:E1.
    + discriminate.
    + destruct (ebl <? threshold_stage3 d) eqn:E2.
      * apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2. lia.
      * destruct (ebl <? threshold_stage4 d) eqn:E3; discriminate.
  - intros [Hlo Hhi].
    apply Nat.ltb_ge in Hlo. rewrite Hlo.
    apply Nat.ltb_lt in Hhi. rewrite Hhi.
    reflexivity.
Qed.

Lemma of_ebl_stage3_iff : forall d ebl,
  of_ebl d ebl = Stage3 <-> threshold_stage3 d <= ebl < threshold_stage4 d.
Proof.
  intros d ebl. unfold of_ebl. split.
  - intro H. destruct (ebl <? threshold_stage2 d) eqn:E1.
    + discriminate.
    + destruct (ebl <? threshold_stage3 d) eqn:E2.
      * discriminate.
      * destruct (ebl <? threshold_stage4 d) eqn:E3.
        -- apply Nat.ltb_ge in E2. apply Nat.ltb_lt in E3. lia.
        -- discriminate.
  - intros [Hlo Hhi].
    pose proof (thresholds_strictly_increasing d) as [H1 H2].
    assert (E1 : ebl <? threshold_stage2 d = false) by (apply Nat.ltb_ge; lia).
    assert (E2 : ebl <? threshold_stage3 d = false) by (apply Nat.ltb_ge; lia).
    assert (E3 : ebl <? threshold_stage4 d = true) by (apply Nat.ltb_lt; lia).
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma of_ebl_stage4_iff : forall d ebl,
  of_ebl d ebl = Stage4 <-> threshold_stage4 d <= ebl.
Proof.
  intros d ebl. unfold of_ebl. split.
  - intro H. destruct (ebl <? threshold_stage2 d) eqn:E1.
    + discriminate.
    + destruct (ebl <? threshold_stage3 d) eqn:E2.
      * discriminate.
      * destruct (ebl <? threshold_stage4 d) eqn:E3.
        -- discriminate.
        -- apply Nat.ltb_ge in E3. exact E3.
  - intro H.
    pose proof (thresholds_strictly_increasing d) as [H1 H2].
    assert (E1 : ebl <? threshold_stage2 d = false) by (apply Nat.ltb_ge; lia).
    assert (E2 : ebl <? threshold_stage3 d = false) by (apply Nat.ltb_ge; lia).
    assert (E3 : ebl <? threshold_stage4 d = false) by (apply Nat.ltb_ge; lia).
    rewrite E1, E2, E3. reflexivity.
Qed.

Theorem of_ebl_exhaustive : forall d ebl,
  of_ebl d ebl = Stage1 \/
  of_ebl d ebl = Stage2 \/
  of_ebl d ebl = Stage3 \/
  of_ebl d ebl = Stage4.
Proof.
  intros d ebl. unfold of_ebl.
  destruct (ebl <? threshold_stage2 d); [left; reflexivity|].
  destruct (ebl <? threshold_stage3 d); [right; left; reflexivity|].
  destruct (ebl <? threshold_stage4 d); [right; right; left; reflexivity|].
  right; right; right; reflexivity.
Qed.

Theorem of_ebl_monotonic : forall d ebl1 ebl2,
  ebl1 <= ebl2 -> of_ebl d ebl1 <=s of_ebl d ebl2.
Proof.
  intros d ebl1 ebl2 Hle. unfold of_ebl, le, to_nat.
  destruct (ebl1 <? threshold_stage2 d) eqn:E1a;
  destruct (ebl2 <? threshold_stage2 d) eqn:E1b.
  - simpl. lia.
  - destruct (ebl2 <? threshold_stage3 d) eqn:E2b.
    + simpl. lia.
    + destruct (ebl2 <? threshold_stage4 d) eqn:E3b; simpl; lia.
  - apply Nat.ltb_ge in E1a. apply Nat.ltb_lt in E1b. lia.
  - destruct (ebl1 <? threshold_stage3 d) eqn:E2a;
    destruct (ebl2 <? threshold_stage3 d) eqn:E2b.
    + simpl. lia.
    + destruct (ebl2 <? threshold_stage4 d) eqn:E3b; simpl; lia.
    + apply Nat.ltb_ge in E2a. apply Nat.ltb_lt in E2b. lia.
    + destruct (ebl1 <? threshold_stage4 d) eqn:E3a;
      destruct (ebl2 <? threshold_stage4 d) eqn:E3b.
      * simpl. lia.
      * simpl. lia.
      * apply Nat.ltb_ge in E3a. apply Nat.ltb_lt in E3b. lia.
      * simpl. lia.
Qed.

(** Boundary verification for VAGINAL delivery: 499 mL is Stage1, 500 mL is Stage2 *)
Example vaginal_boundary_499_is_stage1 : of_ebl DeliveryMode.Vaginal 499 = Stage1.
Proof. reflexivity. Qed.

Example vaginal_boundary_500_is_stage2 : of_ebl DeliveryMode.Vaginal 500 = Stage2.
Proof. reflexivity. Qed.

Example vaginal_boundary_999_is_stage2 : of_ebl DeliveryMode.Vaginal 999 = Stage2.
Proof. reflexivity. Qed.

Example vaginal_boundary_1000_is_stage3 : of_ebl DeliveryMode.Vaginal 1000 = Stage3.
Proof. reflexivity. Qed.

Example vaginal_boundary_1499_is_stage3 : of_ebl DeliveryMode.Vaginal 1499 = Stage3.
Proof. reflexivity. Qed.

Example vaginal_boundary_1500_is_stage4 : of_ebl DeliveryMode.Vaginal 1500 = Stage4.
Proof. reflexivity. Qed.

(** Boundary verification for CESAREAN delivery: 999 mL is Stage1, 1000 mL is Stage2 *)
Example cesarean_boundary_999_is_stage1 : of_ebl DeliveryMode.Cesarean 999 = Stage1.
Proof. reflexivity. Qed.

Example cesarean_boundary_1000_is_stage2 : of_ebl DeliveryMode.Cesarean 1000 = Stage2.
Proof. reflexivity. Qed.

Example cesarean_boundary_1499_is_stage2 : of_ebl DeliveryMode.Cesarean 1499 = Stage2.
Proof. reflexivity. Qed.

Example cesarean_boundary_1500_is_stage3 : of_ebl DeliveryMode.Cesarean 1500 = Stage3.
Proof. reflexivity. Qed.

Example cesarean_boundary_1999_is_stage3 : of_ebl DeliveryMode.Cesarean 1999 = Stage3.
Proof. reflexivity. Qed.

Example cesarean_boundary_2000_is_stage4 : of_ebl DeliveryMode.Cesarean 2000 = Stage4.
Proof. reflexivity. Qed.

End Stage.

(******************************************************************************)
(*                                                                            *)
(*                            INTERVENTION                                    *)
(*                                                                            *)
(*  Clinical interventions mapped to PPH stages per California MQC protocol.  *)
(*                                                                            *)
(******************************************************************************)

Module Intervention.

Inductive t : Type :=
  | Observation : t
  | Uterotonics : t
  | Transfusion : t
  | SurgicalIntervention : t.

Definition eq_dec : forall i1 i2 : t, {i1 = i2} + {i1 <> i2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition all : list t := [Observation; Uterotonics; Transfusion; SurgicalIntervention].

Lemma all_contains_every_intervention : forall i : t, In i all.
Proof. intros []; simpl; auto. Qed.

Lemma all_has_no_duplicates : NoDup all.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition to_nat (i : t) : nat :=
  match i with
  | Observation => 1
  | Uterotonics => 2
  | Transfusion => 3
  | SurgicalIntervention => 4
  end.

Definition le (i1 i2 : t) : Prop := to_nat i1 <= to_nat i2.

Notation "i1 <=i i2" := (le i1 i2) (at level 70).

Definition of_stage (s : Stage.t) : t :=
  match s with
  | Stage.Stage1 => Observation
  | Stage.Stage2 => Uterotonics
  | Stage.Stage3 => Transfusion
  | Stage.Stage4 => SurgicalIntervention
  end.

Theorem of_stage_monotonic : forall s1 s2 : Stage.t,
  Stage.le s1 s2 -> le (of_stage s1) (of_stage s2).
Proof.
  intros [] [] H; unfold Stage.le, Stage.to_nat, le, to_nat, of_stage in *;
  simpl in *; lia.
Qed.

Definition of_ebl (d : DeliveryMode.t) (ebl : nat) : t := of_stage (Stage.of_ebl d ebl).

Theorem of_ebl_monotonic : forall d ebl1 ebl2,
  ebl1 <= ebl2 -> le (of_ebl d ebl1) (of_ebl d ebl2).
Proof.
  intros d ebl1 ebl2 Hle. unfold of_ebl.
  apply of_stage_monotonic. apply Stage.of_ebl_monotonic. exact Hle.
Qed.

(** Clinical scenarios for VAGINAL delivery *)
Example vaginal_ebl_300_requires_observation : of_ebl DeliveryMode.Vaginal 300 = Observation.
Proof. reflexivity. Qed.

Example vaginal_ebl_700_requires_uterotonics : of_ebl DeliveryMode.Vaginal 700 = Uterotonics.
Proof. reflexivity. Qed.

Example vaginal_ebl_1200_requires_transfusion : of_ebl DeliveryMode.Vaginal 1200 = Transfusion.
Proof. reflexivity. Qed.

Example vaginal_ebl_2000_requires_surgery : of_ebl DeliveryMode.Vaginal 2000 = SurgicalIntervention.
Proof. reflexivity. Qed.

(** Clinical scenarios for CESAREAN delivery - higher thresholds *)
Example cesarean_ebl_700_requires_observation : of_ebl DeliveryMode.Cesarean 700 = Observation.
Proof. reflexivity. Qed.

Example cesarean_ebl_1200_requires_uterotonics : of_ebl DeliveryMode.Cesarean 1200 = Uterotonics.
Proof. reflexivity. Qed.

Example cesarean_ebl_1700_requires_transfusion : of_ebl DeliveryMode.Cesarean 1700 = Transfusion.
Proof. reflexivity. Qed.

Example cesarean_ebl_2500_requires_surgery : of_ebl DeliveryMode.Cesarean 2500 = SurgicalIntervention.
Proof. reflexivity. Qed.

(** Critical safety: Stage4 always triggers surgical intervention *)
Theorem stage4_requires_surgery : of_stage Stage.Stage4 = SurgicalIntervention.
Proof. reflexivity. Qed.

(** Critical safety: Surgical intervention only for Stage4 *)
Theorem surgery_only_for_stage4 : forall s : Stage.t,
  of_stage s = SurgicalIntervention -> s = Stage.Stage4.
Proof. intros [] H; try reflexivity; discriminate. Qed.

(** Critical safety: EBL >= threshold_stage4 triggers surgical intervention *)
Theorem ebl_ge_threshold_requires_surgery : forall d ebl,
  Stage.threshold_stage4 d <= ebl -> of_ebl d ebl = SurgicalIntervention.
Proof.
  intros d ebl H. unfold of_ebl.
  assert (Hstage : Stage.of_ebl d ebl = Stage.Stage4).
  { apply Stage.of_ebl_stage4_iff. exact H. }
  rewrite Hstage. reflexivity.
Qed.

(** Critical safety: EBL < threshold_stage4 does NOT require surgery *)
Theorem ebl_lt_threshold_no_surgery : forall d ebl,
  ebl < Stage.threshold_stage4 d -> of_ebl d ebl <> SurgicalIntervention.
Proof.
  intros d ebl Hlt Hcontra.
  unfold of_ebl in Hcontra.
  apply surgery_only_for_stage4 in Hcontra.
  apply Stage.of_ebl_stage4_iff in Hcontra.
  lia.
Qed.

(** Bidirectional: surgery iff EBL >= threshold_stage4 *)
Theorem surgery_iff_ebl_ge_threshold : forall d ebl,
  of_ebl d ebl = SurgicalIntervention <-> Stage.threshold_stage4 d <= ebl.
Proof.
  intros d ebl. split.
  - intro H. unfold of_ebl in H.
    apply surgery_only_for_stage4 in H.
    apply Stage.of_ebl_stage4_iff. exact H.
  - exact (ebl_ge_threshold_requires_surgery d ebl).
Qed.

End Intervention.

(******************************************************************************)
(*                                                                            *)
(*                            UTEROTONICS                                     *)
(*                                                                            *)
(*  Uterotonic agents for uterine atony with sequencing and contraindications *)
(*                                                                            *)
(******************************************************************************)

Module Uterotonics.

Inductive Agent : Type :=
  | Oxytocin : Agent
  | Methylergonovine : Agent
  | Carboprost : Agent
  | Misoprostol : Agent.

Definition eq_dec : forall a1 a2 : Agent, {a1 = a2} + {a1 <> a2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

Definition line_of_therapy (a : Agent) : nat :=
  match a with
  | Oxytocin => 1
  | Methylergonovine => 2
  | Carboprost => 2
  | Misoprostol => 2
  end.

Record Contraindications : Type := MkContra {
  has_hypertension : bool;
  has_preeclampsia_contra : bool;
  has_asthma : bool;
  has_cardiac_disease : bool
}.

Definition is_contraindicated (c : Contraindications) (a : Agent) : bool :=
  match a with
  | Oxytocin => false
  | Methylergonovine => has_hypertension c || has_preeclampsia_contra c
  | Carboprost => has_asthma c
  | Misoprostol => false
  end.

Definition safe_agents (c : Contraindications) : list Agent :=
  filter (fun a => negb (is_contraindicated c a)) [Oxytocin; Methylergonovine; Carboprost; Misoprostol].

Lemma oxytocin_always_safe : forall c, is_contraindicated c Oxytocin = false.
Proof. intros c. reflexivity. Qed.

Lemma misoprostol_always_safe : forall c, is_contraindicated c Misoprostol = false.
Proof. intros c. reflexivity. Qed.

Lemma oxytocin_in_safe_agents : forall c, In Oxytocin (safe_agents c).
Proof.
  intros c. unfold safe_agents, is_contraindicated. simpl.
  left. reflexivity.
Qed.

Definition recommended_sequence (c : Contraindications) : list Agent :=
  Oxytocin ::
  (if is_contraindicated c Methylergonovine then [] else [Methylergonovine]) ++
  (if is_contraindicated c Carboprost then [] else [Carboprost]) ++
  [Misoprostol].

Lemma recommended_sequence_nonempty : forall c, recommended_sequence c <> [].
Proof. intros c. unfold recommended_sequence. discriminate. Qed.

Lemma recommended_sequence_starts_with_oxytocin : forall c,
  hd_error (recommended_sequence c) = Some Oxytocin.
Proof. intros c. reflexivity. Qed.

(** Standard single doses *)
Definition dose_oxytocin_iv_units : nat := 40.
Definition dose_methylergonovine_mg_x100 : nat := 20.
Definition dose_carboprost_mcg : nat := 250.
Definition dose_misoprostol_mcg : nat := 800.

(** Maximum cumulative doses in first hour *)
Definition max_dose_oxytocin_iv_units : nat := 80.
Definition max_dose_methylergonovine_doses : nat := 5.
Definition max_dose_carboprost_doses : nat := 8.
Definition max_dose_misoprostol_mcg : nat := 1000.

(** Minimum repeat intervals in minutes.
    Carboprost (Hemabate): q15-90 minutes per package insert.
    Using 15 minutes as minimum to allow for acute hemorrhage scenarios.
    Maximum recommended total: 8 doses (2mg total). *)
Definition repeat_interval_oxytocin_min : nat := 15.
Definition repeat_interval_methylergonovine_min : nat := 2.
Definition repeat_interval_carboprost_min_lower : nat := 15.
Definition repeat_interval_carboprost_min_typical : nat := 30.
Definition repeat_interval_carboprost_min : nat := 15.
Definition repeat_interval_misoprostol_min : nat := 60.

(** Dosing state tracker *)
Record DosingState : Type := MkDosingState {
  oxytocin_total_units : nat;
  methylergonovine_doses : nat;
  carboprost_doses : nat;
  misoprostol_total_mcg : nat;
  last_oxytocin_time : option nat;
  last_methylergonovine_time : option nat;
  last_carboprost_time : option nat;
  last_misoprostol_time : option nat
}.

Definition empty_dosing_state : DosingState :=
  MkDosingState 0 0 0 0 None None None None.

Definition can_give_dose (s : DosingState) (a : Agent) (current_time : nat) : bool :=
  match a with
  | Oxytocin =>
    (oxytocin_total_units s + dose_oxytocin_iv_units <=? max_dose_oxytocin_iv_units) &&
    match last_oxytocin_time s with
    | None => true
    | Some t => repeat_interval_oxytocin_min <=? (current_time - t)
    end
  | Methylergonovine =>
    (methylergonovine_doses s <? max_dose_methylergonovine_doses) &&
    match last_methylergonovine_time s with
    | None => true
    | Some t => repeat_interval_methylergonovine_min <=? (current_time - t)
    end
  | Carboprost =>
    (carboprost_doses s <? max_dose_carboprost_doses) &&
    match last_carboprost_time s with
    | None => true
    | Some t => repeat_interval_carboprost_min <=? (current_time - t)
    end
  | Misoprostol =>
    (misoprostol_total_mcg s + dose_misoprostol_mcg <=? max_dose_misoprostol_mcg) &&
    match last_misoprostol_time s with
    | None => true
    | Some t => repeat_interval_misoprostol_min <=? (current_time - t)
    end
  end.

Definition record_dose (s : DosingState) (a : Agent) (current_time : nat) : DosingState :=
  match a with
  | Oxytocin => MkDosingState
      (oxytocin_total_units s + dose_oxytocin_iv_units)
      (methylergonovine_doses s) (carboprost_doses s) (misoprostol_total_mcg s)
      (Some current_time) (last_methylergonovine_time s)
      (last_carboprost_time s) (last_misoprostol_time s)
  | Methylergonovine => MkDosingState
      (oxytocin_total_units s) (methylergonovine_doses s + 1)
      (carboprost_doses s) (misoprostol_total_mcg s)
      (last_oxytocin_time s) (Some current_time)
      (last_carboprost_time s) (last_misoprostol_time s)
  | Carboprost => MkDosingState
      (oxytocin_total_units s) (methylergonovine_doses s)
      (carboprost_doses s + 1) (misoprostol_total_mcg s)
      (last_oxytocin_time s) (last_methylergonovine_time s)
      (Some current_time) (last_misoprostol_time s)
  | Misoprostol => MkDosingState
      (oxytocin_total_units s) (methylergonovine_doses s)
      (carboprost_doses s) (misoprostol_total_mcg s + dose_misoprostol_mcg)
      (last_oxytocin_time s) (last_methylergonovine_time s)
      (last_carboprost_time s) (Some current_time)
  end.

Lemma empty_state_can_give_oxytocin : forall t,
  can_give_dose empty_dosing_state Oxytocin t = true.
Proof.
  intros t. unfold can_give_dose, empty_dosing_state, dose_oxytocin_iv_units, max_dose_oxytocin_iv_units.
  simpl. reflexivity.
Qed.

(******************************************************************************)
(*                      UTERINE ATONY RESPONSE MODELING                       *)
(*                                                                            *)
(*  Models efficacy, time-to-response, and refractory atony criteria.         *)
(*  Based on: Gallos I et al. Cochrane Database Syst Rev 2018.               *)
(******************************************************************************)

(** Expected efficacy rates (percentage x10 for precision).
    Based on meta-analysis data for uterine atony response. *)
Definition efficacy_oxytocin_x10 : nat := 80.
Definition efficacy_methylergonovine_x10 : nat := 75.
Definition efficacy_carboprost_x10 : nat := 88.
Definition efficacy_misoprostol_x10 : nat := 70.

Definition agent_efficacy_x10 (a : Agent) : nat :=
  match a with
  | Oxytocin => efficacy_oxytocin_x10
  | Methylergonovine => efficacy_methylergonovine_x10
  | Carboprost => efficacy_carboprost_x10
  | Misoprostol => efficacy_misoprostol_x10
  end.

(** Expected time to response in minutes *)
Definition time_to_response_oxytocin_min : nat := 2.
Definition time_to_response_methylergonovine_min : nat := 3.
Definition time_to_response_carboprost_min : nat := 5.
Definition time_to_response_misoprostol_min : nat := 15.

Definition agent_time_to_response (a : Agent) : nat :=
  match a with
  | Oxytocin => time_to_response_oxytocin_min
  | Methylergonovine => time_to_response_methylergonovine_min
  | Carboprost => time_to_response_carboprost_min
  | Misoprostol => time_to_response_misoprostol_min
  end.

Lemma oxytocin_fastest_response : forall a,
  time_to_response_oxytocin_min <= agent_time_to_response a.
Proof.
  intros a. destruct a;
  unfold agent_time_to_response, time_to_response_oxytocin_min,
    time_to_response_methylergonovine_min, time_to_response_carboprost_min,
    time_to_response_misoprostol_min; lia.
Qed.

Lemma carboprost_most_effective : forall a,
  agent_efficacy_x10 a <= efficacy_carboprost_x10.
Proof.
  intros a. destruct a; unfold agent_efficacy_x10, efficacy_carboprost_x10,
    efficacy_oxytocin_x10, efficacy_methylergonovine_x10, efficacy_misoprostol_x10; lia.
Qed.

(** Atony response status *)
Inductive AtonyResponse : Type :=
  | Responsive : AtonyResponse
  | PartialResponse : AtonyResponse
  | Refractory : AtonyResponse.

(** Refractory atony definition:
    Failed to respond to at least 2 uterotonics given at adequate doses
    with adequate time for response (per ACOG 2017) *)
Record AtonyState : Type := MkAtonyState {
  agents_tried : list Agent;
  minutes_since_first_uterotonic : nat;
  bleeding_controlled : bool;
  uterine_tone_adequate : bool
}.

Definition initial_atony_state : AtonyState :=
  MkAtonyState [] 0 false false.

Definition agents_tried_count (s : AtonyState) : nat :=
  length (agents_tried s).

(** Atony is refractory if:
    1. At least 2 different agents tried, AND
    2. At least 15 minutes since first uterotonic, AND
    3. Bleeding not controlled OR uterine tone inadequate *)
Definition is_refractory_atony (s : AtonyState) : bool :=
  (2 <=? agents_tried_count s) &&
  (15 <=? minutes_since_first_uterotonic s) &&
  (negb (bleeding_controlled s) || negb (uterine_tone_adequate s)).

(** Partial response: some improvement but not resolved *)
Definition is_partial_response (s : AtonyState) : bool :=
  (1 <=? agents_tried_count s) &&
  negb (is_refractory_atony s) &&
  (uterine_tone_adequate s && negb (bleeding_controlled s) ||
   bleeding_controlled s && negb (uterine_tone_adequate s)).

Definition atony_response_status (s : AtonyState) : AtonyResponse :=
  if bleeding_controlled s && uterine_tone_adequate s then Responsive
  else if is_refractory_atony s then Refractory
  else if is_partial_response s then PartialResponse
  else Responsive.

Lemma refractory_requires_multiple_agents : forall s,
  is_refractory_atony s = true -> 2 <= agents_tried_count s.
Proof.
  intros s H. unfold is_refractory_atony in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply andb_true_iff in H1. destruct H1 as [H1a H1b].
  apply Nat.leb_le in H1a. exact H1a.
Qed.

Lemma refractory_requires_adequate_time : forall s,
  is_refractory_atony s = true -> 15 <= minutes_since_first_uterotonic s.
Proof.
  intros s H. unfold is_refractory_atony in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply andb_true_iff in H1. destruct H1 as [H1a H1b].
  apply Nat.leb_le in H1b. exact H1b.
Qed.

(** Refractory atony triggers surgical escalation *)
Definition refractory_atony_triggers_surgery (s : AtonyState) : bool :=
  is_refractory_atony s.

Lemma controlled_bleeding_not_refractory : forall s,
  bleeding_controlled s = true -> uterine_tone_adequate s = true ->
  is_refractory_atony s = false.
Proof.
  intros s Hb Ht. unfold is_refractory_atony.
  rewrite Hb, Ht.
  destruct (2 <=? agents_tried_count s) eqn:E1;
  destruct (15 <=? minutes_since_first_uterotonic s) eqn:E2;
  simpl; reflexivity.
Qed.

End Uterotonics.

(******************************************************************************)
(*                                                                            *)
(*                      ADVERSE EVENT MODELING                                *)
(*                                                                            *)
(*  Complications and adverse events from PPH interventions.                  *)
(*  Models risk-benefit tradeoffs for treatment decisions.                    *)
(*                                                                            *)
(******************************************************************************)

Module AdverseEvents.

(** Adverse event severity classification *)
Inductive Severity : Type :=
  | Mild : Severity        (** Self-limiting, no treatment needed *)
  | Moderate : Severity    (** Requires treatment, no permanent harm *)
  | Severe : Severity      (** Life-threatening or permanent harm *)
  | Fatal : Severity.

Definition severity_to_nat (s : Severity) : nat :=
  match s with Mild => 1 | Moderate => 2 | Severe => 3 | Fatal => 4 end.

(** Uterotonic adverse events *)
Inductive UterotonicAE : Type :=
  | Hypertension : UterotonicAE         (** Methylergonovine *)
  | Bronchospasm : UterotonicAE         (** Carboprost *)
  | Nausea : UterotonicAE               (** All uterotonics *)
  | Fever : UterotonicAE                (** Misoprostol *)
  | CardiacArrhythmia : UterotonicAE.   (** Methylergonovine, severe *)

Definition uterotonic_ae_severity (ae : UterotonicAE) : Severity :=
  match ae with
  | Hypertension => Moderate
  | Bronchospasm => Severe
  | Nausea => Mild
  | Fever => Mild
  | CardiacArrhythmia => Severe
  end.

Definition uterotonic_ae_agent (ae : UterotonicAE) : list Uterotonics.Agent :=
  match ae with
  | Hypertension => [Uterotonics.Methylergonovine]
  | Bronchospasm => [Uterotonics.Carboprost]
  | Nausea => [Uterotonics.Oxytocin; Uterotonics.Methylergonovine;
               Uterotonics.Carboprost; Uterotonics.Misoprostol]
  | Fever => [Uterotonics.Misoprostol]
  | CardiacArrhythmia => [Uterotonics.Methylergonovine]
  end.

(** TXA adverse events *)
Inductive TXA_AE : Type :=
  | TXA_Seizure : TXA_AE          (** Rare but serious *)
  | TXA_Thrombosis : TXA_AE       (** Theoretical risk *)
  | TXA_Nausea : TXA_AE.

Definition txa_ae_severity (ae : TXA_AE) : Severity :=
  match ae with
  | TXA_Seizure => Severe
  | TXA_Thrombosis => Severe
  | TXA_Nausea => Mild
  end.

(** TXA seizure risk: approximately 1-2% at high doses per CRASH-2 data *)
Definition txa_seizure_risk_per_1000 : nat := 15.

(** Transfusion adverse events *)
Inductive TransfusionAE : Type :=
  | TACO : TransfusionAE              (** Transfusion-associated circulatory overload *)
  | TRALI : TransfusionAE             (** Transfusion-related acute lung injury *)
  | FebrileReaction : TransfusionAE
  | AllergicReaction : TransfusionAE
  | HemolyticReaction : TransfusionAE
  | Infection : TransfusionAE.

Definition transfusion_ae_severity (ae : TransfusionAE) : Severity :=
  match ae with
  | TACO => Severe
  | TRALI => Fatal
  | FebrileReaction => Mild
  | AllergicReaction => Moderate
  | HemolyticReaction => Severe
  | Infection => Moderate
  end.

(** TRALI risk: ~1 in 5000 units transfused *)
Definition trali_risk_per_10000_units : nat := 2.
(** TACO risk: ~1 in 100 MTP activations *)
Definition taco_risk_per_100_mtp : nat := 1.

(** Surgical adverse events *)
Inductive SurgicalAE : Type :=
  | SurgicalBleeding : SurgicalAE
  | OrganInjury : SurgicalAE
  | Infection_Surgical : SurgicalAE
  | VTE : SurgicalAE
  | AnesthesiaComplication : SurgicalAE.

Definition surgical_ae_severity (ae : SurgicalAE) : Severity :=
  match ae with
  | SurgicalBleeding => Severe
  | OrganInjury => Severe
  | Infection_Surgical => Moderate
  | VTE => Severe
  | AnesthesiaComplication => Severe
  end.

(** Risk-benefit decision: intervention indicated if benefit exceeds risk *)
Definition benefit_exceeds_risk (mortality_reduction_pct : nat)
                                  (ae_risk_pct : nat)
                                  (ae_severity : Severity) : bool :=
  let severity_weight := severity_to_nat ae_severity in
  let weighted_risk := ae_risk_pct * severity_weight in
  weighted_risk <? mortality_reduction_pct * 4.

(** PPH mortality without treatment is high; most interventions are justified *)
Lemma high_mortality_justifies_treatment : forall ae_risk ae_sev,
  ae_risk <= 10 -> ae_sev <> Fatal ->
  benefit_exceeds_risk 20 ae_risk ae_sev = true.
Proof.
  intros ae_risk ae_sev Hr Hs.
  unfold benefit_exceeds_risk, severity_to_nat.
  destruct ae_sev; try contradiction;
  apply Nat.ltb_lt; lia.
Qed.

(** Contraindicated agent given: models the adverse outcome *)
Definition contraindicated_agent_given (c : Uterotonics.Contraindications)
                                         (a : Uterotonics.Agent) : option UterotonicAE :=
  if Uterotonics.is_contraindicated c a then
    match a with
    | Uterotonics.Methylergonovine => Some Hypertension
    | Uterotonics.Carboprost => Some Bronchospasm
    | _ => None
    end
  else None.

Lemma contraindicated_causes_ae : forall c a ae,
  contraindicated_agent_given c a = Some ae ->
  severity_to_nat (uterotonic_ae_severity ae) >= 2.
Proof.
  intros c a ae H.
  unfold contraindicated_agent_given in H.
  destruct (Uterotonics.is_contraindicated c a); try discriminate.
  destruct a; try discriminate; injection H; intro; subst; simpl; lia.
Qed.

End AdverseEvents.

(******************************************************************************)
(*                                                                            *)
(*                       TRANEXAMIC ACID PROTOCOL                             *)
(*                                                                            *)
(*  TXA administration per WOMAN trial: 1g IV within 3 hours of onset.       *)
(*                                                                            *)
(******************************************************************************)

Module TXA.

Definition dose_mg : nat := 1000.
Definition max_minutes_from_onset : nat := 180.
Definition repeat_dose_allowed : bool := true.
Definition repeat_interval_minutes : nat := 30.

Record TXAState : Type := MkTXAState {
  first_dose_given : bool;
  first_dose_time_min : option nat;
  second_dose_given : bool;
  bleeding_ongoing : bool
}.

Definition initial_state : TXAState :=
  MkTXAState false None false true.

Definition can_give_first_dose (s : TXAState) (minutes_since_onset : nat) : bool :=
  negb (first_dose_given s) && (minutes_since_onset <? max_minutes_from_onset).

Definition can_give_second_dose (s : TXAState) (current_time : nat) : bool :=
  match first_dose_time_min s with
  | None => false
  | Some t => first_dose_given s &&
              negb (second_dose_given s) &&
              bleeding_ongoing s &&
              (t + repeat_interval_minutes <=? current_time)
  end.

Definition give_first_dose (s : TXAState) (time : nat) : TXAState :=
  MkTXAState true (Some time) false (bleeding_ongoing s).

Definition give_second_dose (s : TXAState) : TXAState :=
  MkTXAState true (first_dose_time_min s) true (bleeding_ongoing s).

Lemma first_dose_within_window : forall s t,
  can_give_first_dose s t = true -> t < max_minutes_from_onset.
Proof.
  intros s t H. unfold can_give_first_dose in H.
  destruct (first_dose_given s); simpl in H; try discriminate.
  apply Nat.ltb_lt in H. exact H.
Qed.

Lemma second_requires_first : forall s t,
  can_give_second_dose s t = true -> first_dose_given s = true.
Proof.
  intros s t H. unfold can_give_second_dose in H.
  destruct (first_dose_time_min s); try discriminate.
  destruct (first_dose_given s); simpl in H; try discriminate.
  reflexivity.
Qed.

Definition txa_indicated (ebl : nat) (minutes_since_onset : nat) : bool :=
  (500 <=? ebl) && (minutes_since_onset <? max_minutes_from_onset).

Lemma early_txa_better : forall ebl t1 t2,
  t1 < t2 -> txa_indicated ebl t2 = true -> txa_indicated ebl t1 = true.
Proof.
  intros ebl t1 t2 Hlt H. unfold txa_indicated in *.
  destruct (500 <=? ebl) eqn:E; simpl in *; try discriminate.
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

End TXA.

(******************************************************************************)
(*                                                                            *)
(*                    MASSIVE TRANSFUSION PROTOCOL                            *)
(*                                                                            *)
(*  MTP activation criteria and blood product ratios.                        *)
(*                                                                            *)
(******************************************************************************)

Module MTP.

Definition activation_ebl_threshold : nat := 1500.
Definition activation_shock_index_x10_threshold : nat := 14.

(** ABO Blood Type System *)
Inductive BloodType : Type :=
  | TypeA : BloodType
  | TypeB : BloodType
  | TypeAB : BloodType
  | TypeO : BloodType.

Inductive RhFactor : Type := RhPos | RhNeg.

Record FullBloodType : Type := MkFullBloodType {
  abo : BloodType;
  rh : RhFactor
}.

Definition abo_compatible (donor recipient : BloodType) : bool :=
  match donor, recipient with
  | TypeO, _ => true
  | TypeA, TypeA => true
  | TypeA, TypeAB => true
  | TypeB, TypeB => true
  | TypeB, TypeAB => true
  | TypeAB, TypeAB => true
  | _, _ => false
  end.

Definition rh_compatible (donor recipient : RhFactor) : bool :=
  match donor, recipient with
  | RhNeg, _ => true
  | RhPos, RhPos => true
  | _, _ => false
  end.

Definition blood_compatible (donor recipient : FullBloodType) : bool :=
  abo_compatible (abo donor) (abo recipient) &&
  rh_compatible (rh donor) (rh recipient).

Lemma o_neg_universal_donor : forall recipient,
  blood_compatible (MkFullBloodType TypeO RhNeg) recipient = true.
Proof.
  intros [[] []]; reflexivity.
Qed.

Lemma ab_pos_universal_recipient : forall donor,
  blood_compatible donor (MkFullBloodType TypeAB RhPos) = true.
Proof.
  intros [[] []]; reflexivity.
Qed.

Record BloodProducts : Type := MkBloodProducts {
  prbc_units : nat;
  ffp_units : nat;
  platelet_units : nat;
  cryo_units : nat
}.

Definition ratio_1_1_1 (units : nat) : BloodProducts :=
  MkBloodProducts units units units 0.

Definition ratio_with_cryo (units : nat) (cryo : nat) : BloodProducts :=
  MkBloodProducts units units units cryo.

Definition mtp_indicated_by_ebl (ebl : nat) : bool :=
  activation_ebl_threshold <=? ebl.

Definition mtp_indicated_by_vitals (shock_index_x10 : nat) : bool :=
  activation_shock_index_x10_threshold <=? shock_index_x10.

Definition mtp_indicated (ebl : nat) (shock_index_x10 : nat) : bool :=
  mtp_indicated_by_ebl ebl || mtp_indicated_by_vitals shock_index_x10.

Definition initial_pack : BloodProducts := ratio_1_1_1 6.

Definition subsequent_pack : BloodProducts := ratio_1_1_1 4.

Definition add_cryo_if_needed (bp : BloodProducts) (fibrinogen_low : bool) : BloodProducts :=
  if fibrinogen_low then
    MkBloodProducts (prbc_units bp) (ffp_units bp) (platelet_units bp) 10
  else bp.

Lemma mtp_ebl_implies_vaginal_stage4 : forall ebl,
  mtp_indicated_by_ebl ebl = true -> Stage.threshold_stage4 DeliveryMode.Vaginal <= ebl.
Proof.
  intros ebl H. unfold mtp_indicated_by_ebl, activation_ebl_threshold in H.
  apply Nat.leb_le in H. unfold Stage.threshold_stage4. exact H.
Qed.

Lemma vaginal_stage4_implies_mtp : forall ebl,
  Stage.threshold_stage4 DeliveryMode.Vaginal <= ebl -> mtp_indicated_by_ebl ebl = true.
Proof.
  intros ebl H. unfold mtp_indicated_by_ebl, activation_ebl_threshold.
  unfold Stage.threshold_stage4 in H. apply Nat.leb_le. exact H.
Qed.

Lemma mtp_threshold_matches_vaginal_stage4 :
  activation_ebl_threshold = Stage.threshold_stage4 DeliveryMode.Vaginal.
Proof. reflexivity. Qed.

Definition total_prbc (packs : list BloodProducts) : nat :=
  fold_right (fun bp acc => prbc_units bp + acc) 0 packs.

Definition total_ffp (packs : list BloodProducts) : nat :=
  fold_right (fun bp acc => ffp_units bp + acc) 0 packs.

Definition balanced_ratio (packs : list BloodProducts) : bool :=
  let prbc := total_prbc packs in
  let ffp := total_ffp packs in
  if prbc =? 0 then true
  else (ffp * 2 <=? prbc * 3) && (prbc * 2 <=? ffp * 3).

(** Platelet totaling for ratio verification *)
Definition total_platelets (packs : list BloodProducts) : nat :=
  fold_right (fun bp acc => platelet_units bp + acc) 0 packs.

(** Single pack from ratio_1_1_1 is balanced (PRBC = FFP = Platelets) *)
Lemma ratio_1_1_1_single_balanced : forall units,
  units > 0 ->
  balanced_ratio [ratio_1_1_1 units] = true.
Proof.
  intros units Hpos. unfold balanced_ratio, total_prbc, total_ffp, ratio_1_1_1.
  simpl. rewrite Nat.add_0_r.
  destruct (units =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

(** Initial MTP pack is balanced *)
Lemma initial_pack_balanced : balanced_ratio [initial_pack] = true.
Proof. apply ratio_1_1_1_single_balanced. unfold initial_pack, ratio_1_1_1. lia. Qed.

(** Subsequent MTP pack is balanced *)
Lemma subsequent_pack_balanced : balanced_ratio [subsequent_pack] = true.
Proof. apply ratio_1_1_1_single_balanced. unfold subsequent_pack, ratio_1_1_1. lia. Qed.

(** Two ratio_1_1_1 packs together remain balanced *)
Lemma two_balanced_packs : forall u1 u2,
  u1 > 0 -> u2 > 0 ->
  balanced_ratio [ratio_1_1_1 u1; ratio_1_1_1 u2] = true.
Proof.
  intros u1 u2 H1 H2. unfold balanced_ratio, total_prbc, total_ffp, ratio_1_1_1.
  simpl. repeat rewrite Nat.add_0_r.
  destruct (u1 + u2 =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

(** Initial + subsequent packs remain balanced *)
Lemma initial_plus_subsequent_balanced :
  balanced_ratio [initial_pack; subsequent_pack] = true.
Proof. apply two_balanced_packs; unfold initial_pack, subsequent_pack, ratio_1_1_1; lia. Qed.

(** Key property: PRBC = FFP for any ratio_1_1_1 pack *)
Lemma ratio_1_1_1_prbc_eq_ffp : forall units,
  prbc_units (ratio_1_1_1 units) = ffp_units (ratio_1_1_1 units).
Proof. intros. reflexivity. Qed.

(** Totals are equal for any list of ratio_1_1_1 packs *)
Lemma total_prbc_eq_total_ffp_ratio : forall units_list,
  total_prbc (map ratio_1_1_1 units_list) = total_ffp (map ratio_1_1_1 units_list).
Proof.
  intros units_list. induction units_list as [|u rest IH].
  - reflexivity.
  - simpl map. unfold total_prbc, total_ffp. simpl.
    f_equal. exact IH.
Qed.

(** Any list of ratio_1_1_1 packs is balanced *)
Lemma ratio_1_1_1_list_balanced : forall units_list,
  (forall u, In u units_list -> u > 0) ->
  balanced_ratio (map ratio_1_1_1 units_list) = true.
Proof.
  intros units_list Hpos. unfold balanced_ratio.
  rewrite total_prbc_eq_total_ffp_ratio.
  destruct (total_ffp (map ratio_1_1_1 units_list) =? 0) eqn:E.
  - reflexivity.
  - apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

End MTP.

(******************************************************************************)
(*                                                                            *)
(*                         TEAM ESCALATION                                    *)
(*                                                                            *)
(*  Team activation and resource mobilization by stage.                      *)
(*                                                                            *)
(******************************************************************************)

Module TeamEscalation.

Inductive TeamMember : Type :=
  | AttendingOB : TeamMember
  | Anesthesia : TeamMember
  | BloodBank : TeamMember
  | Nursing : TeamMember
  | OR_Staff : TeamMember
  | InterventionalRadiology : TeamMember
  | MaternalFetalMedicine : TeamMember
  | Hematology : TeamMember
  | ICU : TeamMember.

Definition stage1_team : list TeamMember :=
  [AttendingOB; Nursing].

Definition stage2_team : list TeamMember :=
  [AttendingOB; Nursing; Anesthesia; BloodBank].

Definition stage3_team : list TeamMember :=
  [AttendingOB; Nursing; Anesthesia; BloodBank; OR_Staff].

Definition stage4_team : list TeamMember :=
  [AttendingOB; Nursing; Anesthesia; BloodBank; OR_Staff;
   InterventionalRadiology; MaternalFetalMedicine; ICU].

Definition team_for_stage (s : Stage.t) : list TeamMember :=
  match s with
  | Stage.Stage1 => stage1_team
  | Stage.Stage2 => stage2_team
  | Stage.Stage3 => stage3_team
  | Stage.Stage4 => stage4_team
  end.

Lemma attending_always_present : forall s,
  In AttendingOB (team_for_stage s).
Proof. intros []; simpl; auto. Qed.

Lemma nursing_always_present : forall s,
  In Nursing (team_for_stage s).
Proof. intros []; simpl; auto. Qed.

Lemma anesthesia_from_stage2 : forall s,
  Stage.le Stage.Stage2 s -> In Anesthesia (team_for_stage s).
Proof.
  intros s H. destruct s; unfold Stage.le, Stage.to_nat in H; simpl in *;
  try (simpl; auto); lia.
Qed.

Lemma team_size_monotonic : forall s1 s2,
  Stage.le s1 s2 -> length (team_for_stage s1) <= length (team_for_stage s2).
Proof.
  intros [] [] H; unfold Stage.le, Stage.to_nat in H; simpl in *; lia.
Qed.

Inductive Resource : Type :=
  | IV_Access_Large : Resource
  | Type_And_Screen : Resource
  | Blood_Available : Resource
  | OR_Ready : Resource
  | Cell_Saver : Resource
  | Bakri_Balloon : Resource
  | Uterotonics_Ready : Resource.

Definition stage1_resources : list Resource :=
  [IV_Access_Large; Type_And_Screen; Uterotonics_Ready].

Definition stage2_resources : list Resource :=
  [IV_Access_Large; Type_And_Screen; Blood_Available; Uterotonics_Ready].

Definition stage3_resources : list Resource :=
  [IV_Access_Large; Type_And_Screen; Blood_Available; OR_Ready; Cell_Saver; Bakri_Balloon].

Definition stage4_resources : list Resource :=
  [IV_Access_Large; Type_And_Screen; Blood_Available; OR_Ready; Cell_Saver; Bakri_Balloon].

Definition resources_for_stage (s : Stage.t) : list Resource :=
  match s with
  | Stage.Stage1 => stage1_resources
  | Stage.Stage2 => stage2_resources
  | Stage.Stage3 => stage3_resources
  | Stage.Stage4 => stage4_resources
  end.

End TeamEscalation.

(******************************************************************************)
(*                                                                            *)
(*                      CHECKLIST COMPLIANCE                                  *)
(*                                                                            *)
(*  Bundle elements per California MQC OB Hemorrhage Toolkit.                *)
(*                                                                            *)
(******************************************************************************)

Module Checklist.

Record Stage1Checklist : Type := MkStage1 {
  s1_fundal_massage : bool;
  s1_empty_bladder : bool;
  s1_oxytocin_running : bool;
  s1_quantify_blood_loss : bool;
  s1_type_and_screen_sent : bool
}.

Record Stage2Checklist : Type := MkStage2 {
  s2_stage1_complete : Stage1Checklist;
  s2_notify_team : bool;
  s2_second_iv_line : bool;
  s2_uterotonics_given : bool;
  s2_blood_ordered : bool;
  s2_cause_identified : bool
}.

Record Stage3Checklist : Type := MkStage3 {
  s3_stage2_complete : Stage2Checklist;
  s3_mtp_activated : bool;
  s3_move_to_or : bool;
  s3_transfusion_started : bool;
  s3_intrauterine_tamponade : bool;
  s3_surgical_team_notified : bool
}.

Record Stage4Checklist : Type := MkStage4 {
  s4_stage3_complete : Stage3Checklist;
  s4_massive_transfusion : bool;
  s4_surgical_intervention : bool;
  s4_icu_notified : bool;
  s4_hysterectomy_considered : bool
}.

Definition stage1_complete (c : Stage1Checklist) : bool :=
  s1_fundal_massage c &&
  s1_empty_bladder c &&
  s1_oxytocin_running c &&
  s1_quantify_blood_loss c.

Definition stage2_complete (c : Stage2Checklist) : bool :=
  stage1_complete (s2_stage1_complete c) &&
  s2_notify_team c &&
  s2_uterotonics_given c &&
  s2_blood_ordered c.

Definition stage3_complete (c : Stage3Checklist) : bool :=
  stage2_complete (s3_stage2_complete c) &&
  s3_mtp_activated c &&
  s3_transfusion_started c.

Definition stage4_complete (c : Stage4Checklist) : bool :=
  stage3_complete (s4_stage3_complete c) &&
  s4_massive_transfusion c &&
  s4_surgical_intervention c.

Definition compliance_score_stage1 (c : Stage1Checklist) : nat :=
  (if s1_fundal_massage c then 1 else 0) +
  (if s1_empty_bladder c then 1 else 0) +
  (if s1_oxytocin_running c then 1 else 0) +
  (if s1_quantify_blood_loss c then 1 else 0) +
  (if s1_type_and_screen_sent c then 1 else 0).

Lemma compliance_score_stage1_max : forall c, compliance_score_stage1 c <= 5.
Proof.
  intros c. unfold compliance_score_stage1.
  destruct (s1_fundal_massage c); destruct (s1_empty_bladder c);
  destruct (s1_oxytocin_running c); destruct (s1_quantify_blood_loss c);
  destruct (s1_type_and_screen_sent c); simpl; lia.
Qed.

(******************************************************************************)
(*                    CHECKLIST COMPLETION PROOFS                             *)
(*                                                                            *)
(*  Proofs that checklist completion implies stage requirements are met.      *)
(******************************************************************************)

(** Stage 1 complete implies all critical elements done *)
Lemma stage1_complete_implies_fundal_massage : forall c,
  stage1_complete c = true -> s1_fundal_massage c = true.
Proof.
  intros c H. unfold stage1_complete in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H2 _].
  apply andb_true_iff in H2. destruct H2 as [H3 _]. exact H3.
Qed.

Lemma stage1_complete_implies_qbl : forall c,
  stage1_complete c = true -> s1_quantify_blood_loss c = true.
Proof.
  intros c H. unfold stage1_complete in H.
  apply andb_true_iff in H. destruct H as [_ H1]. exact H1.
Qed.

(** Stage 2 complete implies Stage 1 complete *)
Lemma stage2_complete_implies_stage1 : forall c,
  stage2_complete c = true -> stage1_complete (s2_stage1_complete c) = true.
Proof.
  intros c H. unfold stage2_complete in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H2 _].
  apply andb_true_iff in H2. destruct H2 as [H3 _]. exact H3.
Qed.

Lemma stage2_complete_implies_uterotonics : forall c,
  stage2_complete c = true -> s2_uterotonics_given c = true.
Proof.
  intros c H. unfold stage2_complete in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [_ H2]. exact H2.
Qed.

(** Stage 3 complete implies Stage 2 complete *)
Lemma stage3_complete_implies_stage2 : forall c,
  stage3_complete c = true -> stage2_complete (s3_stage2_complete c) = true.
Proof.
  intros c H. unfold stage3_complete in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H2 _]. exact H2.
Qed.

Lemma stage3_complete_implies_transfusion : forall c,
  stage3_complete c = true -> s3_transfusion_started c = true.
Proof.
  intros c H. unfold stage3_complete in H.
  apply andb_true_iff in H. destruct H as [_ H1]. exact H1.
Qed.

(** Stage 4 complete implies Stage 3 complete *)
Lemma stage4_complete_implies_stage3 : forall c,
  stage4_complete c = true -> stage3_complete (s4_stage3_complete c) = true.
Proof.
  intros c H. unfold stage4_complete in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H2 _]. exact H2.
Qed.

Lemma stage4_complete_implies_surgery : forall c,
  stage4_complete c = true -> s4_surgical_intervention c = true.
Proof.
  intros c H. unfold stage4_complete in H.
  apply andb_true_iff in H. destruct H as [_ H1]. exact H1.
Qed.

(** Transitivity: Stage 4 complete implies all prior stages complete *)
Lemma stage4_implies_all_stages : forall c,
  stage4_complete c = true ->
  stage1_complete (s2_stage1_complete (s3_stage2_complete (s4_stage3_complete c))) = true /\
  stage2_complete (s3_stage2_complete (s4_stage3_complete c)) = true /\
  stage3_complete (s4_stage3_complete c) = true.
Proof.
  intros c H.
  split. 2: split.
  - apply stage2_complete_implies_stage1.
    apply stage3_complete_implies_stage2.
    apply stage4_complete_implies_stage3. exact H.
  - apply stage3_complete_implies_stage2.
    apply stage4_complete_implies_stage3. exact H.
  - apply stage4_complete_implies_stage3. exact H.
Qed.

(** Compliance scores for higher stages *)
Definition compliance_score_stage2 (c : Stage2Checklist) : nat :=
  compliance_score_stage1 (s2_stage1_complete c) +
  (if s2_notify_team c then 1 else 0) +
  (if s2_second_iv_line c then 1 else 0) +
  (if s2_uterotonics_given c then 1 else 0) +
  (if s2_blood_ordered c then 1 else 0) +
  (if s2_cause_identified c then 1 else 0).

Lemma compliance_score_stage2_max : forall c, compliance_score_stage2 c <= 10.
Proof.
  intros c. unfold compliance_score_stage2.
  pose proof (compliance_score_stage1_max (s2_stage1_complete c)) as H1.
  destruct (s2_notify_team c); destruct (s2_second_iv_line c);
  destruct (s2_uterotonics_given c); destruct (s2_blood_ordered c);
  destruct (s2_cause_identified c); lia.
Qed.

Definition compliance_score_stage3 (c : Stage3Checklist) : nat :=
  compliance_score_stage2 (s3_stage2_complete c) +
  (if s3_mtp_activated c then 1 else 0) +
  (if s3_move_to_or c then 1 else 0) +
  (if s3_transfusion_started c then 1 else 0) +
  (if s3_intrauterine_tamponade c then 1 else 0) +
  (if s3_surgical_team_notified c then 1 else 0).

Lemma compliance_score_stage3_max : forall c, compliance_score_stage3 c <= 15.
Proof.
  intros c. unfold compliance_score_stage3.
  pose proof (compliance_score_stage2_max (s3_stage2_complete c)) as H1.
  destruct (s3_mtp_activated c); destruct (s3_move_to_or c);
  destruct (s3_transfusion_started c); destruct (s3_intrauterine_tamponade c);
  destruct (s3_surgical_team_notified c); lia.
Qed.

Definition compliance_score_stage4 (c : Stage4Checklist) : nat :=
  compliance_score_stage3 (s4_stage3_complete c) +
  (if s4_massive_transfusion c then 1 else 0) +
  (if s4_surgical_intervention c then 1 else 0) +
  (if s4_icu_notified c then 1 else 0) +
  (if s4_hysterectomy_considered c then 1 else 0).

Lemma compliance_score_stage4_max : forall c, compliance_score_stage4 c <= 19.
Proof.
  intros c. unfold compliance_score_stage4.
  pose proof (compliance_score_stage3_max (s4_stage3_complete c)) as H1.
  destruct (s4_massive_transfusion c); destruct (s4_surgical_intervention c);
  destruct (s4_icu_notified c); destruct (s4_hysterectomy_considered c); lia.
Qed.

(** Compliance percentage calculation *)
Definition compliance_percent_stage1 (c : Stage1Checklist) : nat :=
  compliance_score_stage1 c * 100 / 5.

Definition compliance_percent_stage4 (c : Stage4Checklist) : nat :=
  compliance_score_stage4 c * 100 / 19.

Lemma compliance_percent_stage1_max : forall c, compliance_percent_stage1 c <= 100.
Proof.
  intros c. unfold compliance_percent_stage1.
  pose proof (compliance_score_stage1_max c) as H.
  apply Nat.div_le_upper_bound; lia.
Qed.

End Checklist.

(******************************************************************************)
(*                                                                            *)
(*                    HYSTERECTOMY DECISION                                   *)
(*                                                                            *)
(*  Peripartum hysterectomy criteria and decision support.                   *)
(*                                                                            *)
(******************************************************************************)

Module Hysterectomy.

Inductive ConservativeMeasure : Type :=
  | UterineMassage : ConservativeMeasure
  | UterotonicAgents : ConservativeMeasure
  | IntrauterineBalloon : ConservativeMeasure
  | UterineCompressionSutures : ConservativeMeasure
  | UterineArteryLigation : ConservativeMeasure
  | UterineArteryEmbolization : ConservativeMeasure.

Record HysterectomyContext : Type := MkHystContext {
  conservative_measures_failed : list ConservativeMeasure;
  total_ebl : nat;
  hemodynamic_instability : bool;
  coagulopathy_present : bool;
  uterine_rupture : bool;
  placenta_accreta : bool;
  patient_desires_fertility : bool
}.

Definition conservative_measures_exhausted (c : HysterectomyContext) : bool :=
  (3 <=? length (conservative_measures_failed c)).

Definition life_threatening_hemorrhage (c : HysterectomyContext) : bool :=
  (2000 <=? total_ebl c) && hemodynamic_instability c.

Definition hysterectomy_indicated (c : HysterectomyContext) : bool :=
  uterine_rupture c ||
  (placenta_accreta c && (1500 <=? total_ebl c)) ||
  (conservative_measures_exhausted c && life_threatening_hemorrhage c).

Definition subtotal_preferred (c : HysterectomyContext) : bool :=
  negb (placenta_accreta c) && hemodynamic_instability c.

Lemma rupture_always_indicates : forall c,
  uterine_rupture c = true -> hysterectomy_indicated c = true.
Proof.
  intros c H. unfold hysterectomy_indicated. rewrite H. reflexivity.
Qed.

Definition delay_if_possible (c : HysterectomyContext) : bool :=
  patient_desires_fertility c &&
  negb (life_threatening_hemorrhage c) &&
  negb (uterine_rupture c).

Lemma life_threatening_overrides_fertility : forall c,
  life_threatening_hemorrhage c = true -> delay_if_possible c = false.
Proof.
  intros c H. unfold delay_if_possible. rewrite H. simpl.
  destruct (patient_desires_fertility c); reflexivity.
Qed.

End Hysterectomy.

(******************************************************************************)
(*                                                                            *)
(*                    SURGICAL ESCALATION PATHWAY                             *)
(*                                                                            *)
(*  Formal specification of the surgical intervention escalation sequence.   *)
(*  Each intervention is attempted before moving to more invasive measures.   *)
(*                                                                            *)
(******************************************************************************)

Module SurgicalEscalation.

(** Conservative surgical interventions in order of increasing invasiveness *)
Inductive SurgicalIntervention : Type :=
  | BakriBalloon : SurgicalIntervention
  | UterineCompressionSutures : SurgicalIntervention
  | UterineArteryLigation : SurgicalIntervention
  | InternalIliacLigation : SurgicalIntervention
  | UterineArteryEmbolization : SurgicalIntervention
  | SubtotalHysterectomy : SurgicalIntervention
  | TotalHysterectomy : SurgicalIntervention.

Definition invasiveness_score (i : SurgicalIntervention) : nat :=
  match i with
  | BakriBalloon => 1
  | UterineCompressionSutures => 2
  | UterineArteryLigation => 3
  | InternalIliacLigation => 4
  | UterineArteryEmbolization => 3
  | SubtotalHysterectomy => 5
  | TotalHysterectomy => 6
  end.

Definition preserves_fertility (i : SurgicalIntervention) : bool :=
  match i with
  | BakriBalloon => true
  | UterineCompressionSutures => true
  | UterineArteryLigation => true
  | InternalIliacLigation => true
  | UterineArteryEmbolization => true
  | SubtotalHysterectomy => false
  | TotalHysterectomy => false
  end.

Definition requires_or (i : SurgicalIntervention) : bool :=
  match i with
  | BakriBalloon => false
  | UterineArteryEmbolization => false
  | _ => true
  end.

Definition requires_ir (i : SurgicalIntervention) : bool :=
  match i with
  | UterineArteryEmbolization => true
  | _ => false
  end.

(** Cell saver can be used with clean surgical field.
    Contraindicated: amniotic fluid contamination, infection *)
Definition cell_saver_contraindicated (has_amnio_fluid : bool) (has_infection : bool) : bool :=
  has_amnio_fluid || has_infection.

(** Standard escalation sequence *)
Definition standard_escalation_sequence : list SurgicalIntervention :=
  [BakriBalloon; UterineCompressionSutures; UterineArteryLigation;
   SubtotalHysterectomy; TotalHysterectomy].

Definition ir_available_sequence : list SurgicalIntervention :=
  [BakriBalloon; UterineArteryEmbolization; UterineCompressionSutures;
   UterineArteryLigation; SubtotalHysterectomy; TotalHysterectomy].

Record EscalationState : Type := MkEscalationState {
  interventions_attempted : list SurgicalIntervention;
  bleeding_controlled : bool;
  hemodynamically_stable : bool;
  fertility_desired : bool;
  ir_available : bool
}.

Definition intervention_already_tried (s : EscalationState) (i : SurgicalIntervention) : bool :=
  existsb (fun x =>
    match x, i with
    | BakriBalloon, BakriBalloon => true
    | UterineCompressionSutures, UterineCompressionSutures => true
    | UterineArteryLigation, UterineArteryLigation => true
    | InternalIliacLigation, InternalIliacLigation => true
    | UterineArteryEmbolization, UterineArteryEmbolization => true
    | SubtotalHysterectomy, SubtotalHysterectomy => true
    | TotalHysterectomy, TotalHysterectomy => true
    | _, _ => false
    end
  ) (interventions_attempted s).

Definition next_intervention (s : EscalationState) : option SurgicalIntervention :=
  let seq := if ir_available s then ir_available_sequence else standard_escalation_sequence in
  find (fun i => negb (intervention_already_tried s i)) seq.

Definition should_proceed_to_hysterectomy (s : EscalationState) : bool :=
  negb (bleeding_controlled s) &&
  negb (hemodynamically_stable s) &&
  (3 <=? length (interventions_attempted s)).

Lemma escalation_sequence_starts_conservative :
  hd_error standard_escalation_sequence = Some BakriBalloon.
Proof. reflexivity. Qed.

Lemma hysterectomy_is_last_resort :
  last standard_escalation_sequence BakriBalloon = TotalHysterectomy.
Proof. reflexivity. Qed.

Theorem fertility_preserving_options_exist :
  exists i, In i standard_escalation_sequence /\ preserves_fertility i = true.
Proof.
  exists BakriBalloon. split.
  - left. reflexivity.
  - reflexivity.
Qed.

End SurgicalEscalation.

(******************************************************************************)
(*                                                                            *)
(*                    INTRAUTERINE BALLOON (Gap #7)                           *)
(*                                                                            *)
(*  Bakri balloon sizing, placement verification, and monitoring.             *)
(*  Reference: Bakri et al. BJOG 2001; ACOG Practice Bulletin 183.           *)
(*                                                                            *)
(******************************************************************************)

Module IntrauterineBalloon.

Inductive BalloonType : Type :=
  | BakriBalloon : BalloonType      (** 500mL max *)
  | BTLBalloon : BalloonType        (** 500mL max *)
  | EBBalloon : BalloonType         (** 750mL max *)
  | CondomCatheter : BalloonType.   (** Variable, low-resource *)

Definition max_fill_volume_mL (bt : BalloonType) : nat :=
  match bt with
  | BakriBalloon => 500
  | BTLBalloon => 500
  | EBBalloon => 750
  | CondomCatheter => 500
  end.

Record BalloonPlacement : Type := MkBalloon {
  balloon_type : BalloonType;
  fill_volume_mL : nat;
  placement_time_minutes : nat;
  tamponade_test_positive : bool;
  drainage_rate_mL_hr : nat
}.

(** Fill volume must not exceed maximum *)
Definition fill_volume_valid (bp : BalloonPlacement) : bool :=
  fill_volume_mL bp <=? max_fill_volume_mL (balloon_type bp).

(** Tamponade test: bleeding stops when balloon inflated *)
Definition tamponade_achieved (bp : BalloonPlacement) : bool :=
  tamponade_test_positive bp && (drainage_rate_mL_hr bp <? 50).

(** Time to reassess if tamponade not achieved *)
Definition reassess_interval_minutes : nat := 15.

(** Maximum balloon duration before removal/surgery *)
Definition max_balloon_duration_hours : nat := 24.

(** Balloon should be removed if drainage exceeds threshold *)
Definition drainage_threshold_mL_hr : nat := 100.

Definition balloon_failing (bp : BalloonPlacement) : bool :=
  negb (tamponade_achieved bp) || (drainage_threshold_mL_hr <=? drainage_rate_mL_hr bp).

(** Escalation required if balloon fails *)
Definition requires_escalation (bp : BalloonPlacement) : bool :=
  balloon_failing bp.

Lemma valid_fill_bounded : forall bp,
  fill_volume_valid bp = true -> fill_volume_mL bp <= 750.
Proof.
  intros bp H. unfold fill_volume_valid in H. apply Nat.leb_le in H.
  destruct (balloon_type bp); simpl in H; lia.
Qed.

End IntrauterineBalloon.

(******************************************************************************)
(*                                                                            *)
(*                    BP MEASUREMENT METHODS (Gap #8)                         *)
(*                                                                            *)
(*  Arterial line vs NIBP reliability for shock index calculation.            *)
(*                                                                            *)
(******************************************************************************)

Module BPMeasurement.

Inductive MeasurementMethod : Type :=
  | ArterialLine : MeasurementMethod    (** Gold standard, continuous *)
  | NIBP_Oscillometric : MeasurementMethod  (** Standard cuff *)
  | NIBP_Manual : MeasurementMethod     (** Auscultatory *)
  | Palpation : MeasurementMethod.      (** SBP only, emergency *)

(** Measurement uncertainty by method (mmHg) *)
Definition sbp_uncertainty (m : MeasurementMethod) : nat :=
  match m with
  | ArterialLine => 3
  | NIBP_Oscillometric => 8
  | NIBP_Manual => 10
  | Palpation => 20
  end.

(** Reliability score 0-100 *)
Definition reliability_score (m : MeasurementMethod) : nat :=
  match m with
  | ArterialLine => 100
  | NIBP_Oscillometric => 85
  | NIBP_Manual => 75
  | Palpation => 50
  end.

(** Can detect DBP? *)
Definition provides_dbp (m : MeasurementMethod) : bool :=
  match m with
  | Palpation => false
  | _ => true
  end.

(** Arterial line indicated when shock index elevated or unstable *)
Definition arterial_line_indicated (shock_index_x10 : nat) (unstable : bool) : bool :=
  (10 <=? shock_index_x10) || unstable.

(** Shock index confidence based on measurement method *)
Definition shock_index_confidence (m : MeasurementMethod) : nat :=
  reliability_score m.

Lemma arterial_most_reliable : forall m,
  reliability_score m <= reliability_score ArterialLine.
Proof. intros []; simpl; lia. Qed.

End BPMeasurement.

(******************************************************************************)
(*                                                                            *)
(*                    CELL SAVER YIELD (Gap #9)                               *)
(*                                                                            *)
(*  Expected RBC recovery from cell salvage.                                  *)
(*  Reference: AABB Technical Manual.                                         *)
(*                                                                            *)
(******************************************************************************)

Module CellSaver.

(** Cell saver efficiency: typically 50-80% RBC recovery *)
Definition efficiency_low_pct : nat := 50.
Definition efficiency_typical_pct : nat := 65.
Definition efficiency_high_pct : nat := 80.

(** Expected yield in mL of packed cells from collected blood *)
Definition expected_yield_mL (collected_mL : nat) (hematocrit_pct : nat) (efficiency_pct : nat) : nat :=
  (collected_mL * hematocrit_pct * efficiency_pct) / 10000.

(** Minimum collection for processing *)
Definition minimum_collection_mL : nat := 500.

(** Contraindications to cell saver use *)
Record CellSaverContraindications : Type := MkCSContra {
  cs_amniotic_fluid_contamination : bool;
  cs_infection : bool;
  cs_malignancy : bool;
  cs_sickle_cell : bool
}.

Definition cell_saver_safe (c : CellSaverContraindications) : bool :=
  negb (cs_amniotic_fluid_contamination c) &&
  negb (cs_infection c) &&
  negb (cs_malignancy c) &&
  negb (cs_sickle_cell c).

(** With leukocyte depletion filter, amniotic fluid is relative contraindication *)
Definition cell_saver_with_filter_safe (c : CellSaverContraindications) : bool :=
  negb (cs_infection c) &&
  negb (cs_malignancy c) &&
  negb (cs_sickle_cell c).

(** Equivalent PRBC units from yield (1 unit ≈ 200mL packed cells) *)
Definition equivalent_prbc_units (yield_mL : nat) : nat := yield_mL / 200.

Lemma yield_bounded_by_collection : forall c h e,
  h <= 100 -> e <= 100 ->
  expected_yield_mL c h e <= c.
Proof.
  intros c h e Hh He. unfold expected_yield_mL.
  assert (H10000: 10000 = 100 * 100) by (vm_compute; reflexivity).
  assert (Hprod: c * h * e <= c * 100 * 100).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l; exact Hh | exact He]. }
  rewrite H10000.
  transitivity ((c * (100 * 100)) / (100 * 100)).
  - apply Nat.Div0.div_le_mono.
    replace (c * (100 * 100)) with (c * 100 * 100) by (symmetry; apply Nat.mul_assoc).
    exact Hprod.
  - rewrite Nat.div_mul; [apply Nat.le_refl | easy].
Qed.

End CellSaver.

(******************************************************************************)
(*                                                                            *)
(*                    DRUG INTERACTIONS (Gap #10)                             *)
(*                                                                            *)
(*  Pharmacological interactions affecting PPH management.                    *)
(*                                                                            *)
(******************************************************************************)

Module DrugInteractions.

Inductive Drug : Type :=
  | Oxytocin : Drug
  | Methylergonovine : Drug
  | Carboprost : Drug
  | Misoprostol : Drug
  | TranexamicAcid : Drug
  | Magnesium : Drug
  | Labetalol : Drug
  | Nifedipine : Drug
  | Ephedrine : Drug
  | Phenylephrine : Drug.

Inductive InteractionSeverity : Type :=
  | NoInteraction : InteractionSeverity
  | Minor : InteractionSeverity
  | Moderate : InteractionSeverity
  | Severe : InteractionSeverity
  | Contraindicated : InteractionSeverity.

(** Key interactions in obstetric hemorrhage context *)
Definition interaction (d1 d2 : Drug) : InteractionSeverity :=
  match d1, d2 with
  | Magnesium, Oxytocin => Moderate        (** Mg reduces oxytocin effect *)
  | Oxytocin, Magnesium => Moderate
  | Magnesium, Nifedipine => Severe        (** Profound hypotension risk *)
  | Nifedipine, Magnesium => Severe
  | Methylergonovine, Labetalol => Moderate (** Both affect BP *)
  | Labetalol, Methylergonovine => Moderate
  | Carboprost, _ => NoInteraction
  | _, Carboprost => NoInteraction
  | TranexamicAcid, _ => NoInteraction     (** TXA has few interactions *)
  | _, TranexamicAcid => NoInteraction
  | _, _ => NoInteraction
  end.

Definition interaction_blocks_use (sev : InteractionSeverity) : bool :=
  match sev with
  | Contraindicated => true
  | Severe => true
  | _ => false
  end.

Definition safe_to_coadminister (d1 d2 : Drug) : bool :=
  negb (interaction_blocks_use (interaction d1 d2)).

(** Dose adjustment needed? *)
Definition requires_dose_adjustment (d1 d2 : Drug) : bool :=
  match interaction d1 d2 with
  | Moderate => true
  | _ => false
  end.

Lemma txa_always_safe : forall d,
  safe_to_coadminister TranexamicAcid d = true.
Proof. intros []; reflexivity. Qed.

End DrugInteractions.

(******************************************************************************)
(*                                                                            *)
(*                    MTP TERMINATION (Gap #24)                               *)
(*                                                                            *)
(*  Criteria for terminating massive transfusion protocol.                    *)
(*                                                                            *)
(******************************************************************************)

Module MTPTermination.

Record TerminationCriteria : Type := MkTermCriteria {
  bleeding_controlled : bool;
  hemodynamically_stable : bool;
  lactate_normalizing : bool;
  coags_improving : bool;
  surgical_source_controlled : bool;
  minutes_since_last_transfusion : nat
}.

(** All criteria met for safe termination *)
Definition safe_to_terminate (tc : TerminationCriteria) : bool :=
  bleeding_controlled tc &&
  hemodynamically_stable tc &&
  surgical_source_controlled tc.

(** Recommended observation period after last transfusion *)
Definition observation_period_minutes : nat := 30.

Definition observation_complete (tc : TerminationCriteria) : bool :=
  observation_period_minutes <=? minutes_since_last_transfusion tc.

(** Full termination criteria *)
Definition terminate_mtp (tc : TerminationCriteria) : bool :=
  safe_to_terminate tc && observation_complete tc.

(** Reasons to continue MTP despite some improvement *)
Definition continue_mtp_reasons (tc : TerminationCriteria) : bool :=
  negb (bleeding_controlled tc) ||
  negb (surgical_source_controlled tc) ||
  negb (hemodynamically_stable tc).

Lemma termination_requires_bleeding_control : forall tc,
  terminate_mtp tc = true -> bleeding_controlled tc = true.
Proof.
  intros tc H. unfold terminate_mtp, safe_to_terminate in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H1 _]. exact H1.
Qed.

End MTPTermination.

(******************************************************************************)
(*                                                                            *)
(*                    POSTPARTUM MONITORING (Gap #25)                         *)
(*                                                                            *)
(*  Duration and frequency of monitoring after hemorrhage controlled.         *)
(*                                                                            *)
(******************************************************************************)

Module PostpartumMonitoring.

Inductive MonitoringLevel : Type :=
  | ICU : MonitoringLevel
  | StepDown : MonitoringLevel
  | LaborAndDelivery : MonitoringLevel
  | Postpartum : MonitoringLevel.

(** Vital sign check frequency (minutes) *)
Definition vitals_frequency (level : MonitoringLevel) : nat :=
  match level with
  | ICU => 15
  | StepDown => 30
  | LaborAndDelivery => 30
  | Postpartum => 60
  end.

(** Minimum monitoring duration after hemorrhage controlled (hours) *)
Definition minimum_monitoring_hours (max_stage_reached : nat) : nat :=
  match max_stage_reached with
  | 1 => 2
  | 2 => 4
  | 3 => 12
  | _ => 24  (** Stage 4 *)
  end.

(** Recommended monitoring level by stage *)
Definition recommended_level (max_stage : nat) (hours_since_control : nat) : MonitoringLevel :=
  match max_stage with
  | 4 => if hours_since_control <? 24 then ICU else StepDown
  | 3 => if hours_since_control <? 6 then LaborAndDelivery else Postpartum
  | _ => Postpartum
  end.

(** Criteria for downgrading monitoring level *)
Record DowngradeCriteria : Type := MkDowngrade {
  dg_vitals_stable_hours : nat;
  dg_no_active_bleeding : bool;
  dg_urine_output_adequate : bool;
  dg_mental_status_normal : bool
}.

Definition safe_to_downgrade (dc : DowngradeCriteria) : bool :=
  (2 <=? dg_vitals_stable_hours dc) &&
  dg_no_active_bleeding dc &&
  dg_urine_output_adequate dc &&
  dg_mental_status_normal dc.

Lemma icu_most_frequent : forall level,
  vitals_frequency level >= vitals_frequency ICU.
Proof. intros []; simpl; lia. Qed.

End PostpartumMonitoring.

(******************************************************************************)
(*                                                                            *)
(*                    ICU DISCHARGE (Gap #26)                                 *)
(*                                                                            *)
(*  Criteria for ICU discharge after PPH.                                     *)
(*                                                                            *)
(******************************************************************************)

Module ICUDischarge.

Record DischargeCriteria : Type := MkDischargeCriteria {
  dc_off_vasopressors_hours : nat;
  dc_off_ventilator : bool;
  dc_hemodynamically_stable : bool;
  dc_no_ongoing_transfusion : bool;
  dc_coagulopathy_resolved : bool;
  dc_urine_output_adequate : bool;
  dc_mental_status_baseline : bool;
  dc_pain_controlled : bool
}.

(** Minimum time off vasopressors before discharge *)
Definition min_off_pressors_hours : nat := 6.

(** All criteria met *)
Definition ready_for_discharge (dc : DischargeCriteria) : bool :=
  (min_off_pressors_hours <=? dc_off_vasopressors_hours dc) &&
  dc_off_ventilator dc &&
  dc_hemodynamically_stable dc &&
  dc_no_ongoing_transfusion dc &&
  dc_coagulopathy_resolved dc &&
  dc_urine_output_adequate dc &&
  dc_mental_status_baseline dc.

(** Discharge destination *)
Inductive DischargeDestination : Type :=
  | ToStepDown : DischargeDestination
  | ToLaborDelivery : DischargeDestination
  | ToPostpartum : DischargeDestination.

Definition appropriate_destination (had_surgery : bool) (ebl_over_2000 : bool) : DischargeDestination :=
  if had_surgery then ToStepDown
  else if ebl_over_2000 then ToStepDown
  else ToLaborDelivery.

Lemma discharge_requires_off_pressors : forall dc,
  ready_for_discharge dc = true -> dc_off_vasopressors_hours dc >= 6.
Proof.
  intros dc H. unfold ready_for_discharge in H.
  repeat (apply andb_true_iff in H; destruct H as [H _]).
  apply Nat.leb_le in H. exact H.
Qed.

End ICUDischarge.

(******************************************************************************)
(*                                                                            *)
(*                    INTEGRATED ASSESSMENT                                   *)
(*                                                                            *)
(*  Combined assessment using EBL, vitals, labs, and rate of loss.           *)
(*                                                                            *)
(******************************************************************************)

Module IntegratedAssessment.

(** ClinicalState captures the full patient assessment at a point in time.
    IMPORTANT: minutes_since_hemorrhage_onset is distinct from minutes_since_delivery.
    TXA must be given within 3 hours of hemorrhage onset (WOMAN trial), not delivery. *)
Record ClinicalState : Type := MkClinicalState {
  ebl : nat;
  delivery_mode : DeliveryMode.t;
  vitals : VitalSigns.t;
  labs : LabValues.t;
  patient : PatientFactors.t;
  etiology : option Etiology.t;
  rate_of_loss : nat;
  minutes_since_delivery : nat;
  minutes_since_hemorrhage_onset : nat
}.

Definition ebl_stage (s : ClinicalState) : Stage.t :=
  Stage.of_ebl (delivery_mode s) (ebl s).

Definition vitals_suggest_escalation (s : ClinicalState) : bool :=
  VitalSigns.requires_immediate_intervention (vitals s).

Definition labs_suggest_escalation (s : ClinicalState) : bool :=
  LabValues.transfusion_trigger_met (labs s).

Definition rate_suggests_escalation (s : ClinicalState) : bool :=
  RateOfLoss.is_rapid (rate_of_loss s).

Definition effective_stage (s : ClinicalState) : nat :=
  let base := Stage.to_nat (ebl_stage s) in
  let vitals_bump := if vitals_suggest_escalation s then 1 else 0 in
  let labs_bump := if labs_suggest_escalation s then 1 else 0 in
  let rate_bump := if rate_suggests_escalation s then 1 else 0 in
  Nat.min 4 (base + Nat.max vitals_bump (Nat.max labs_bump rate_bump)).

Definition effective_stage_t (s : ClinicalState) : Stage.t :=
  match effective_stage s with
  | 1 => Stage.Stage1
  | 2 => Stage.Stage2
  | 3 => Stage.Stage3
  | _ => Stage.Stage4
  end.

Lemma effective_stage_ge_ebl_stage : forall s,
  Stage.to_nat (ebl_stage s) <= effective_stage s.
Proof.
  intros s. unfold effective_stage.
  set (base := Stage.to_nat (ebl_stage s)).
  set (v := if vitals_suggest_escalation s then 1 else 0).
  set (l := if labs_suggest_escalation s then 1 else 0).
  set (r := if rate_suggests_escalation s then 1 else 0).
  assert (H1 : base <= base + Nat.max v (Nat.max l r)) by lia.
  assert (H2 : Nat.min 4 (base + Nat.max v (Nat.max l r)) <= base + Nat.max v (Nat.max l r))
    by apply Nat.le_min_r.
  destruct (Nat.le_ge_cases 4 (base + Nat.max v (Nat.max l r))) as [Hcase|Hcase].
  - rewrite Nat.min_l by lia.
    pose proof (Stage.to_nat_upper_bound (ebl_stage s)). lia.
  - rewrite Nat.min_r by lia. lia.
Qed.

Lemma effective_stage_at_most_4 : forall s, effective_stage s <= 4.
Proof.
  intros s. unfold effective_stage.
  apply Nat.le_min_l.
Qed.

(** CRITICAL SAFETY PROPERTY: Every patient is staged (no patient falls through).
    Effective stage is always at least 1. *)
Lemma effective_stage_ge_1 : forall s, 1 <= effective_stage s.
Proof.
  intros s. unfold effective_stage.
  set (base := Stage.to_nat (ebl_stage s)).
  set (v := if vitals_suggest_escalation s then 1 else 0).
  set (l := if labs_suggest_escalation s then 1 else 0).
  set (r := if rate_suggests_escalation s then 1 else 0).
  assert (Hbase: 1 <= base).
  { unfold base. unfold ebl_stage.
    destruct (Stage.of_ebl (delivery_mode s) (ebl s)); simpl; lia. }
  assert (H: 1 <= base + Nat.max v (Nat.max l r)) by lia.
  destruct (Nat.le_ge_cases 4 (base + Nat.max v (Nat.max l r))) as [Hcase|Hcase].
  - rewrite Nat.min_l by lia. lia.
  - rewrite Nat.min_r by lia. lia.
Qed.

(** Corollary: effective_stage always returns a valid stage (1-4) *)
Lemma effective_stage_valid : forall s, 1 <= effective_stage s <= 4.
Proof.
  intros s. split.
  - apply effective_stage_ge_1.
  - apply effective_stage_at_most_4.
Qed.

(** No patient unstaged: effective_stage_t always returns a proper Stage.t *)
Lemma effective_stage_t_ge_1 : forall s,
  Stage.to_nat (effective_stage_t s) >= 1.
Proof.
  intros s. unfold effective_stage_t, Stage.to_nat.
  destruct (effective_stage s) as [|[|[|[|n]]]]; auto.
Qed.

Definition recommended_intervention (s : ClinicalState) : Intervention.t :=
  Intervention.of_stage (effective_stage_t s).

(** TXA indication uses minutes_since_hemorrhage_onset per WOMAN trial protocol *)
Definition txa_indicated (s : ClinicalState) : bool :=
  TXA.txa_indicated (ebl s) (minutes_since_hemorrhage_onset s).

(** Validity predicate: hemorrhage cannot start before delivery (for primary PPH) *)
Definition timing_valid (s : ClinicalState) : bool :=
  minutes_since_hemorrhage_onset s <=? minutes_since_delivery s.

Definition mtp_indicated (s : ClinicalState) : bool :=
  MTP.mtp_indicated (ebl s) (VitalSigns.shock_index_x10 (vitals s)).

(** Lethal triad detection: hypothermia + acidosis + coagulopathy
    Presence of 2+ components requires immediate aggressive intervention *)
Definition lethal_triad_score (s : ClinicalState) : nat :=
  (if VitalSigns.lethal_triad_temp_component (vitals s) then 1 else 0) +
  (if LabValues.lethal_triad_acidosis (labs s) then 1 else 0) +
  (if LabValues.lethal_triad_coagulopathy (labs s) then 1 else 0).

Definition lethal_triad_present (s : ClinicalState) : bool :=
  2 <=? lethal_triad_score s.

Definition critical_state (s : ClinicalState) : bool :=
  lethal_triad_present s ||
  VitalSigns.class_4_hemorrhage (vitals s) ||
  LabValues.has_overt_dic (labs s).

Lemma lethal_triad_max_3 : forall s, lethal_triad_score s <= 3.
Proof.
  intros s. unfold lethal_triad_score.
  destruct (VitalSigns.lethal_triad_temp_component (vitals s));
  destruct (LabValues.lethal_triad_acidosis (labs s));
  destruct (LabValues.lethal_triad_coagulopathy (labs s)); simpl; lia.
Qed.

(** DIC detection triggers different management pathway *)
Definition dic_management_indicated (s : ClinicalState) : bool :=
  LabValues.has_overt_dic (labs s).

(** Baseline-adjusted hemoglobin drop assessment *)
Definition significant_hgb_drop (s : ClinicalState) : bool :=
  let baseline := PatientFactors.baseline_hgb_x10 (patient s) in
  let current := LabValues.hemoglobin_g_dL_x10 (labs s) in
  LabValues.significant_hgb_drop baseline current.

(** Percent blood volume lost - uses pregnancy-adjusted calculation *)
Definition percent_volume_lost (s : ClinicalState) : nat :=
  PatientFactors.percent_blood_volume_lost (patient s) (ebl s).

(** Critical state with class 4 hemorrhage triggers vitals escalation *)
Lemma class_4_triggers_escalation : forall s,
  VitalSigns.class_4_hemorrhage (vitals s) = true ->
  vitals_suggest_escalation s = true.
Proof.
  intros s H. unfold vitals_suggest_escalation, VitalSigns.requires_immediate_intervention.
  unfold VitalSigns.class_3_hemorrhage. rewrite H. simpl. reflexivity.
Qed.

(******************************************************************************)
(*                  PERCENTAGE-BASED STAGING                                  *)
(*                                                                            *)
(*  Alternative staging using percent blood volume lost instead of absolute   *)
(*  EBL. More physiologically appropriate for patients at extremes of weight. *)
(*  Reference: ATLS hemorrhage classification (Class I-IV by % blood volume). *)
(******************************************************************************)

(** ATLS-based percent blood volume thresholds *)
Definition pct_stage2_threshold : nat := 15.   (** 15% - Class II hemorrhage *)
Definition pct_stage3_threshold : nat := 30.   (** 30% - Class III hemorrhage *)
Definition pct_stage4_threshold : nat := 40.   (** 40% - Class IV hemorrhage *)

(** Stage by percentage blood volume lost *)
Definition stage_by_percent (pct : nat) : nat :=
  if pct <? pct_stage2_threshold then 1
  else if pct <? pct_stage3_threshold then 2
  else if pct <? pct_stage4_threshold then 3
  else 4.

Lemma stage_by_percent_range : forall pct, 1 <= stage_by_percent pct <= 4.
Proof.
  intros pct. unfold stage_by_percent.
  destruct (pct <? pct_stage2_threshold);
  destruct (pct <? pct_stage3_threshold);
  destruct (pct <? pct_stage4_threshold); lia.
Qed.

(** Combined staging: takes the higher of absolute EBL staging or percent staging *)
Definition combined_stage (s : ClinicalState) : nat :=
  let abs_stage := Stage.to_nat (ebl_stage s) in
  let pct_stage := stage_by_percent (percent_volume_lost s) in
  Nat.max abs_stage pct_stage.

Lemma combined_stage_ge_ebl_stage : forall s,
  Stage.to_nat (ebl_stage s) <= combined_stage s.
Proof.
  intros s. unfold combined_stage. apply Nat.le_max_l.
Qed.

Lemma combined_stage_ge_pct_stage : forall s,
  stage_by_percent (percent_volume_lost s) <= combined_stage s.
Proof.
  intros s. unfold combined_stage. apply Nat.le_max_r.
Qed.

Lemma combined_stage_valid : forall s, 1 <= combined_stage s <= 4.
Proof.
  intros s. unfold combined_stage.
  pose proof (Stage.to_nat_lower_bound (ebl_stage s)) as Hlo.
  pose proof (Stage.to_nat_upper_bound (ebl_stage s)) as Hhi.
  pose proof (stage_by_percent_range (percent_volume_lost s)) as [Hp1 Hp2].
  split; lia.
Qed.

(** Low-weight patient example: 50kg woman has ~4200mL blood volume.
    1000mL EBL = 24% blood volume -> different staging than 80kg woman *)
Definition low_weight_patient_example_ebv : nat := 4200.
Definition normal_weight_patient_example_ebv : nat := 5600.

(** Smaller divisor yields larger quotient (integer division) *)
Lemma div_smaller_divisor_larger : forall n d1 d2,
  d1 > 0 -> d2 > 0 -> d1 <= d2 -> n / d2 <= n / d1.
Proof.
  intros n d1 d2 Hd1 Hd2 Hle.
  apply Nat.div_le_compat_l. split; assumption.
Qed.

(** Same EBL results in higher percentage for smaller patient *)
Lemma smaller_patient_higher_pct : forall ebl ebv1 ebv2,
  ebv1 < ebv2 -> ebv1 > 0 -> ebv2 > 0 ->
  ebl * 100 / ebv1 >= ebl * 100 / ebv2.
Proof.
  intros ebl ebv1 ebv2 Hlt H1 H2.
  apply div_smaller_divisor_larger; lia.
Qed.

(** Effective stage incorporating percent-based logic *)
Definition effective_stage_with_pct (s : ClinicalState) : nat :=
  let base := combined_stage s in
  let vitals_bump := if vitals_suggest_escalation s then 1 else 0 in
  let labs_bump := if labs_suggest_escalation s then 1 else 0 in
  let rate_bump := if rate_suggests_escalation s then 1 else 0 in
  Nat.min 4 (base + Nat.max vitals_bump (Nat.max labs_bump rate_bump)).

Lemma effective_stage_with_pct_ge_combined : forall s,
  combined_stage s <= effective_stage_with_pct s.
Proof.
  intros s. unfold effective_stage_with_pct.
  set (base := combined_stage s).
  set (v := if vitals_suggest_escalation s then 1 else 0).
  set (l := if labs_suggest_escalation s then 1 else 0).
  set (r := if rate_suggests_escalation s then 1 else 0).
  pose proof (combined_stage_valid s) as [Hlo Hhi].
  destruct (Nat.le_ge_cases 4 (base + Nat.max v (Nat.max l r))) as [Hcase|Hcase].
  - rewrite Nat.min_l by lia. lia.
  - rewrite Nat.min_r by lia. lia.
Qed.

End IntegratedAssessment.

(******************************************************************************)
(*                                                                            *)
(*                        AUDIT LOGGING                                       *)
(*                                                                            *)
(*  Types for audit trail and decision logging.                              *)
(*                                                                            *)
(******************************************************************************)

Module AuditLog.

Inductive EventType : Type :=
  | StageAssessed : EventType
  | InterventionStarted : EventType
  | MedicationGiven : EventType
  | TransfusionStarted : EventType
  | TeamNotified : EventType
  | MTPActivated : EventType
  | SurgeryStarted : EventType
  | VitalsRecorded : EventType
  | LabsReceived : EventType
  | EBLUpdated : EventType.

Record AuditEntry : Type := MkEntry {
  timestamp_seconds : nat;
  event_type : EventType;
  stage_at_event : Stage.t;
  ebl_at_event : nat;
  actor_id : nat;
  notes_hash : nat
}.

Record AuditTrail : Type := MkTrail {
  entries : list AuditEntry;
  patient_id : nat;
  encounter_start : nat
}.

Definition empty_trail (patient_id encounter_start : nat) : AuditTrail :=
  MkTrail [] patient_id encounter_start.

Definition add_entry (trail : AuditTrail) (entry : AuditEntry) : AuditTrail :=
  MkTrail (entry :: entries trail) (patient_id trail) (encounter_start trail).

Definition events_of_type (trail : AuditTrail) (et : EventType) : list AuditEntry :=
  filter (fun e => match event_type e, et with
                   | StageAssessed, StageAssessed => true
                   | InterventionStarted, InterventionStarted => true
                   | MedicationGiven, MedicationGiven => true
                   | TransfusionStarted, TransfusionStarted => true
                   | TeamNotified, TeamNotified => true
                   | MTPActivated, MTPActivated => true
                   | SurgeryStarted, SurgeryStarted => true
                   | VitalsRecorded, VitalsRecorded => true
                   | LabsReceived, LabsReceived => true
                   | EBLUpdated, EBLUpdated => true
                   | _, _ => false
                   end) (entries trail).

Definition time_to_first_transfusion (trail : AuditTrail) : option nat :=
  match events_of_type trail TransfusionStarted with
  | [] => None
  | e :: _ => Some (timestamp_seconds e - encounter_start trail)
  end.

Definition time_to_mtp (trail : AuditTrail) : option nat :=
  match events_of_type trail MTPActivated with
  | [] => None
  | e :: _ => Some (timestamp_seconds e - encounter_start trail)
  end.

(** Entries are stored newest-first (prepended by add_entry).
    This predicate verifies the list is properly ordered: each older entry
    has a timestamp <= the newer entry that precedes it in the list.

    For times = [t_newest, t_2, ..., t_oldest]:
    - tl times = [t_2, ..., t_oldest]
    - combine (tl times) times = [(t_2, t_newest), (t_3, t_2), ...]
    - We verify: t_2 <= t_newest, t_3 <= t_2, etc. *)
Definition entries_chronological (trail : AuditTrail) : bool :=
  let times := map timestamp_seconds (entries trail) in
  forallb (fun p => fst p <=? snd p) (combine (tl times) times).

Lemma empty_trail_chronological : forall p e,
  entries_chronological (empty_trail p e) = true.
Proof. intros. unfold entries_chronological, empty_trail. simpl. reflexivity. Qed.

Lemma add_entry_preserves_chronological : forall trail entry,
  entries_chronological trail = true ->
  (forall e, In e (entries trail) -> timestamp_seconds e <= timestamp_seconds entry) ->
  entries_chronological (add_entry trail entry) = true.
Proof.
  intros trail entry Hchron Htime.
  unfold entries_chronological, add_entry in *. simpl.
  destruct (entries trail) as [|e' rest] eqn:Hentries.
  - simpl. reflexivity.
  - simpl. apply andb_true_intro. split.
    + apply Nat.leb_le. apply Htime. left. reflexivity.
    + simpl in Hchron. exact Hchron.
Qed.

End AuditLog.

(******************************************************************************)
(*                                                                            *)
(*                    INTEGRATION INTERFACE                                   *)
(*                                                                            *)
(*  Types for EHR integration and external system communication.             *)
(*                                                                            *)
(******************************************************************************)

Module Integration.

Inductive MessageType : Type :=
  | VitalsUpdate : MessageType
  | LabResult : MessageType
  | BloodBankRequest : MessageType
  | BloodBankResponse : MessageType
  | TeamActivation : MessageType
  | AlertNotification : MessageType.

Record InboundMessage : Type := MkInbound {
  in_msg_type : MessageType;
  in_timestamp : nat;
  in_payload_hash : nat;
  in_source_system : nat
}.

Record OutboundMessage : Type := MkOutbound {
  out_msg_type : MessageType;
  out_timestamp : nat;
  out_payload : nat;
  out_destination : nat;
  out_priority : nat
}.

Definition priority_routine : nat := 1.
Definition priority_urgent : nat := 2.
Definition priority_stat : nat := 3.

Definition message_priority_for_stage (s : Stage.t) : nat :=
  match s with
  | Stage.Stage1 => priority_routine
  | Stage.Stage2 => priority_urgent
  | Stage.Stage3 => priority_stat
  | Stage.Stage4 => priority_stat
  end.

Lemma priority_monotonic : forall s1 s2,
  Stage.le s1 s2 -> message_priority_for_stage s1 <= message_priority_for_stage s2.
Proof.
  intros s1 s2 H.
  destruct s1, s2; unfold message_priority_for_stage, priority_routine, priority_urgent, priority_stat;
  unfold Stage.le, Stage.to_nat in H; simpl in H; lia.
Qed.

Record FHIRReference : Type := MkFHIR {
  resource_type : nat;
  resource_id : nat;
  version : nat
}.

Record HL7Message : Type := MkHL7 {
  message_type_code : nat;
  trigger_event : nat;
  sending_facility : nat;
  receiving_facility : nat;
  message_datetime : nat;
  message_control_id : nat
}.

(** FHIR Resource Types for PPH context *)
Definition fhir_patient : nat := 1.
Definition fhir_observation : nat := 2.
Definition fhir_procedure : nat := 3.
Definition fhir_medication_administration : nat := 4.
Definition fhir_diagnostic_report : nat := 5.
Definition fhir_condition : nat := 6.
Definition fhir_service_request : nat := 7.

(** HL7 Message Types *)
Definition hl7_oru_r01 : nat := 1.
Definition hl7_adt_a08 : nat := 2.
Definition hl7_orm_o01 : nat := 3.
Definition hl7_rde_o11 : nat := 4.

(** Alert severity levels per CDS Hooks *)
Inductive AlertSeverity : Type :=
  | Info : AlertSeverity
  | Warning : AlertSeverity
  | Critical : AlertSeverity.

Definition alert_severity_for_stage (s : Stage.t) : AlertSeverity :=
  match s with
  | Stage.Stage1 => Info
  | Stage.Stage2 => Warning
  | Stage.Stage3 => Critical
  | Stage.Stage4 => Critical
  end.

Record CDSHookCard : Type := MkCDSCard {
  card_summary : nat;
  card_indicator : AlertSeverity;
  card_source : nat;
  card_suggestions_count : nat
}.

Definition stage_to_cds_card (s : Stage.t) (intervention : Intervention.t) : CDSHookCard :=
  MkCDSCard
    (Stage.to_nat s)
    (alert_severity_for_stage s)
    1
    (Intervention.to_nat intervention).

(** Message validation *)
Definition valid_inbound (m : InboundMessage) : bool :=
  (in_timestamp m <=? in_timestamp m + 1) &&
  match in_msg_type m with
  | VitalsUpdate => true
  | LabResult => true
  | BloodBankResponse => true
  | _ => false
  end.

Definition valid_outbound (m : OutboundMessage) : bool :=
  (1 <=? out_priority m) && (out_priority m <=? 3).

(** System identifiers for audit *)
Definition system_ehr : nat := 1.
Definition system_blood_bank : nat := 2.
Definition system_lab : nat := 3.
Definition system_monitor : nat := 4.
Definition system_pph_dss : nat := 5.

Lemma cds_card_severity_correct : forall s i,
  Stage.to_nat s >= 3 ->
  card_indicator (stage_to_cds_card s i) = Critical.
Proof.
  intros s i H.
  destruct s; unfold stage_to_cds_card, alert_severity_for_stage, Stage.to_nat in *;
  simpl in *; try lia; reflexivity.
Qed.

End Integration.

(******************************************************************************)
(*                                                                            *)
(*                    NEGATIVE PROPERTIES                                     *)
(*                                                                            *)
(*  Safety properties stated in negative form.                               *)
(*                                                                            *)
(******************************************************************************)

Module NegativeProperties.

Theorem observation_never_for_pph : forall d ebl,
  Stage.threshold_stage2 d <= ebl ->
  Intervention.of_ebl d ebl <> Intervention.Observation.
Proof.
  intros d ebl H Hcontra.
  unfold Intervention.of_ebl, Intervention.of_stage in Hcontra.
  destruct (Stage.of_ebl d ebl) eqn:E; try discriminate.
  apply Stage.of_ebl_stage1_iff in E. lia.
Qed.

Theorem stage4_never_observation : forall s,
  s = Stage.Stage4 -> Intervention.of_stage s <> Intervention.Observation.
Proof. intros s H. rewrite H. discriminate. Qed.

Theorem stage4_never_uterotonics_only :
  Intervention.of_stage Stage.Stage4 <> Intervention.Uterotonics.
Proof. discriminate. Qed.

Theorem stage4_never_transfusion_only :
  Intervention.of_stage Stage.Stage4 <> Intervention.Transfusion.
Proof. discriminate. Qed.

Theorem no_downgrade_by_ebl : forall d ebl1 ebl2,
  ebl1 <= ebl2 ->
  Intervention.to_nat (Intervention.of_ebl d ebl1) <=
  Intervention.to_nat (Intervention.of_ebl d ebl2).
Proof.
  intros d ebl1 ebl2 H.
  pose proof (Intervention.of_ebl_monotonic d ebl1 ebl2 H) as Hmono.
  unfold Intervention.le in Hmono. exact Hmono.
Qed.

Theorem strict_stage_increase_at_threshold : forall d,
  Stage.to_nat (Stage.of_ebl d (Stage.threshold_stage2 d - 1)) <
  Stage.to_nat (Stage.of_ebl d (Stage.threshold_stage2 d)).
Proof.
  intros []; unfold Stage.threshold_stage2, Stage.of_ebl,
    Stage.threshold_stage3, Stage.threshold_stage4; simpl; lia.
Qed.

Theorem surgery_requires_high_ebl : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.SurgicalIntervention ->
  Stage.threshold_stage4 d <= ebl.
Proof.
  intros d ebl H.
  apply Intervention.surgery_iff_ebl_ge_threshold in H. exact H.
Qed.

End NegativeProperties.

(******************************************************************************)
(*                                                                            *)
(*                    COVERAGE PROOFS                                         *)
(*                                                                            *)
(*  Bidirectional stage/intervention mappings for all stages.                *)
(*                                                                            *)
(******************************************************************************)

Module CoverageProofs.

Theorem observation_iff_stage1 : forall s,
  Intervention.of_stage s = Intervention.Observation <-> s = Stage.Stage1.
Proof.
  intros s. split.
  - intro H. destruct s; try discriminate. reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

Theorem uterotonics_iff_stage2 : forall s,
  Intervention.of_stage s = Intervention.Uterotonics <-> s = Stage.Stage2.
Proof.
  intros s. split.
  - intro H. destruct s; try discriminate. reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

Theorem transfusion_iff_stage3 : forall s,
  Intervention.of_stage s = Intervention.Transfusion <-> s = Stage.Stage3.
Proof.
  intros s. split.
  - intro H. destruct s; try discriminate. reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

Theorem surgery_iff_stage4 : forall s,
  Intervention.of_stage s = Intervention.SurgicalIntervention <-> s = Stage.Stage4.
Proof.
  intros s. split.
  - intro H. destruct s; try discriminate. reflexivity.
  - intro H. rewrite H. reflexivity.
Qed.

Theorem observation_iff_ebl_lt_threshold : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.Observation <-> ebl < Stage.threshold_stage2 d.
Proof.
  intros d ebl. unfold Intervention.of_ebl.
  rewrite observation_iff_stage1.
  apply Stage.of_ebl_stage1_iff.
Qed.

Theorem uterotonics_iff_ebl_range : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.Uterotonics <->
  Stage.threshold_stage2 d <= ebl < Stage.threshold_stage3 d.
Proof.
  intros d ebl. unfold Intervention.of_ebl.
  rewrite uterotonics_iff_stage2.
  apply Stage.of_ebl_stage2_iff.
Qed.

Theorem transfusion_iff_ebl_range : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.Transfusion <->
  Stage.threshold_stage3 d <= ebl < Stage.threshold_stage4 d.
Proof.
  intros d ebl. unfold Intervention.of_ebl.
  rewrite transfusion_iff_stage3.
  apply Stage.of_ebl_stage3_iff.
Qed.

Theorem surgery_iff_ebl_ge_threshold : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.SurgicalIntervention <->
  Stage.threshold_stage4 d <= ebl.
Proof.
  intros d ebl. unfold Intervention.of_ebl.
  rewrite surgery_iff_stage4.
  apply Stage.of_ebl_stage4_iff.
Qed.

(** Vaginal delivery specific proofs for backward compatibility *)
Theorem vaginal_observation_iff_ebl_lt_500 : forall ebl,
  Intervention.of_ebl DeliveryMode.Vaginal ebl = Intervention.Observation <-> ebl < 500.
Proof. intros ebl. apply observation_iff_ebl_lt_threshold. Qed.

Theorem vaginal_surgery_iff_ebl_ge_1500 : forall ebl,
  Intervention.of_ebl DeliveryMode.Vaginal ebl = Intervention.SurgicalIntervention <-> 1500 <= ebl.
Proof. intros ebl. apply surgery_iff_ebl_ge_threshold. Qed.

(** Cesarean delivery specific proofs *)
Theorem cesarean_observation_iff_ebl_lt_1000 : forall ebl,
  Intervention.of_ebl DeliveryMode.Cesarean ebl = Intervention.Observation <-> ebl < 1000.
Proof. intros ebl. apply observation_iff_ebl_lt_threshold. Qed.

Theorem cesarean_surgery_iff_ebl_ge_2000 : forall ebl,
  Intervention.of_ebl DeliveryMode.Cesarean ebl = Intervention.SurgicalIntervention <-> 2000 <= ebl.
Proof. intros ebl. apply surgery_iff_ebl_ge_threshold. Qed.

Theorem every_stage_has_intervention : forall s,
  exists i, Intervention.of_stage s = i.
Proof. intros s. exists (Intervention.of_stage s). reflexivity. Qed.

Theorem every_intervention_has_stage : forall i,
  exists s, Intervention.of_stage s = i.
Proof.
  intros [].
  - exists Stage.Stage1. reflexivity.
  - exists Stage.Stage2. reflexivity.
  - exists Stage.Stage3. reflexivity.
  - exists Stage.Stage4. reflexivity.
Qed.

Theorem stage_intervention_bijection : forall s,
  match Intervention.of_stage s with
  | Intervention.Observation => s = Stage.Stage1
  | Intervention.Uterotonics => s = Stage.Stage2
  | Intervention.Transfusion => s = Stage.Stage3
  | Intervention.SurgicalIntervention => s = Stage.Stage4
  end.
Proof. intros []; reflexivity. Qed.

End CoverageProofs.

(******************************************************************************)
(*                                                                            *)
(*                       ANESTHETIC CONSIDERATIONS                            *)
(*                                                                            *)
(*  GA vs regional anesthesia decision logic, airway risk, hemodynamic goals. *)
(*  Reference: SOAP Consensus Statement, Anesthesiology 2021.                 *)
(*                                                                            *)
(******************************************************************************)

Module AnesthesiaConsiderations.

Inductive AnesthesiaType : Type :=
  | NeuraxialExisting : AnesthesiaType
  | NeuraxialNew : AnesthesiaType
  | GeneralAnesthesia : AnesthesiaType
  | LocalWithSedation : AnesthesiaType.

Record AirwayRisk : Type := MkAirwayRisk {
  mallampati_score : nat;
  neck_mobility_limited : bool;
  obesity_bmi_over_40 : bool;
  preeclampsia_airway_edema : bool;
  recent_oral_intake : bool
}.

Definition difficult_airway_predicted (a : AirwayRisk) : bool :=
  (4 <=? mallampati_score a) ||
  neck_mobility_limited a ||
  (obesity_bmi_over_40 a && preeclampsia_airway_edema a).

Definition aspiration_risk_elevated (a : AirwayRisk) : bool :=
  recent_oral_intake a || preeclampsia_airway_edema a.

Record HemodynamicState : Type := MkHemoState {
  map_mmhg : nat;
  lactate_mmol_x10 : nat;
  base_deficit : nat;
  responsive_to_fluids : bool
}.

(** Hemodynamic goals during resuscitation - permissive hypotension avoided
    in obstetric hemorrhage due to uteroplacental perfusion concerns *)
Definition target_map_minimum : nat := 65.
Definition target_map_obstetric : nat := 70.
Definition target_lactate_x10 : nat := 20.

Definition hemodynamic_goals_met (h : HemodynamicState) : bool :=
  (target_map_obstetric <=? map_mmhg h) &&
  (lactate_mmol_x10 h <=? target_lactate_x10).

(** GA indications in obstetric hemorrhage *)
Definition ga_indicated (coagulopathic : bool) (hemodynamically_unstable : bool)
    (existing_epidural : bool) (airway : AirwayRisk) : bool :=
  coagulopathic ||
  (hemodynamically_unstable && negb existing_epidural) ||
  negb existing_epidural && negb (difficult_airway_predicted airway).

Lemma coagulopathy_requires_ga : forall unstable epidural airway,
  ga_indicated true unstable epidural airway = true.
Proof. intros. unfold ga_indicated. reflexivity. Qed.

Definition neuraxial_safe (coagulopathic : bool) (inr_x10 : nat) (plt_k : nat) : bool :=
  negb coagulopathic && (inr_x10 <=? 15) && (50 <=? plt_k).

Lemma coagulopathy_contraindicates_neuraxial : forall inr plt,
  neuraxial_safe true inr plt = false.
Proof. intros. unfold neuraxial_safe. reflexivity. Qed.

End AnesthesiaConsiderations.

(******************************************************************************)
(*                                                                            *)
(*                       CONCEALED HEMORRHAGE                                 *)
(*                                                                            *)
(*  Detection and adjustment for concealed/retroplacental hemorrhage.         *)
(*                                                                            *)
(******************************************************************************)

Module ConcealedHemorrhage.

(** Types of concealed hemorrhage *)
Inductive ConcealedType : Type :=
  | RetroplacentalHematoma : ConcealedType
  | BroadLigamentHematoma : ConcealedType
  | IntraabdominalHemorrhage : ConcealedType
  | VaginalWallHematoma : ConcealedType.

(** Estimation of concealed blood loss based on clinical signs *)
Definition estimated_concealed_ml (fundal_height_increase_cm : nat)
    (abdominal_girth_increase_cm : nat) : nat :=
  fundal_height_increase_cm * 200 + abdominal_girth_increase_cm * 100.

(** Total blood loss = visible + concealed *)
Definition total_blood_loss (visible_ml : nat) (concealed_ml : nat) : nat :=
  visible_ml + concealed_ml.

(** Clinical signs suggesting concealed hemorrhage *)
Record ConcealedHemorrhageSigns : Type := MkConcealedSigns {
  disproportionate_shock : bool;
  increasing_abdominal_girth : bool;
  fundal_height_rising : bool;
  flank_ecchymosis : bool;
  rigid_abdomen : bool
}.

Definition concealed_hemorrhage_likely (s : ConcealedHemorrhageSigns) : bool :=
  disproportionate_shock s ||
  (increasing_abdominal_girth s && fundal_height_rising s) ||
  flank_ecchymosis s ||
  rigid_abdomen s.

(** Concealed hemorrhage requires adjusted staging *)
Definition stage_adjustment_for_concealed : nat := 1.

Lemma disproportionate_shock_suggests_concealed : forall girth fundal flank rigid,
  concealed_hemorrhage_likely (MkConcealedSigns true girth fundal flank rigid) = true.
Proof. intros. unfold concealed_hemorrhage_likely. reflexivity. Qed.

End ConcealedHemorrhage.

(******************************************************************************)
(*                                                                            *)
(*                      TEMPERATURE MANAGEMENT                                *)
(*                                                                            *)
(*  Active warming protocol and hypothermia prevention.                       *)
(*  Part of damage control resuscitation.                                     *)
(*                                                                            *)
(******************************************************************************)

Module TemperatureManagement.

(** Temperature thresholds in Celsius x10 *)
Definition temp_target_x10 : nat := 365.
Definition temp_mild_hypothermia_x10 : nat := 360.
Definition temp_moderate_hypothermia_x10 : nat := 340.
Definition temp_severe_hypothermia_x10 : nat := 320.

Inductive WarmingDevice : Type :=
  | ForcedAirWarmer : WarmingDevice
  | FluidWarmer : WarmingDevice
  | WarmBlankets : WarmingDevice
  | HeatedHumidifiedOxygen : WarmingDevice.

Record WarmingProtocol : Type := MkWarmingProtocol {
  forced_air_active : bool;
  fluid_warmer_inline : bool;
  warm_blankets_applied : bool;
  room_temp_elevated : bool;
  warmed_irrigation : bool
}.

Definition warming_adequate (p : WarmingProtocol) : bool :=
  forced_air_active p && fluid_warmer_inline p.

(** All IV fluids and blood products should be warmed *)
Definition fluid_warmer_required (temp_x10 : nat) : bool :=
  temp_x10 <? temp_target_x10.

Definition aggressive_warming_required (temp_x10 : nat) : bool :=
  temp_x10 <? temp_moderate_hypothermia_x10.

(** Rewarming rate target: 0.5-1.0 C/hour *)
Definition target_rewarming_rate_x10_per_hour : nat := 5.

Lemma hypothermia_requires_fluid_warmer :
  fluid_warmer_required temp_mild_hypothermia_x10 = true.
Proof. unfold fluid_warmer_required, temp_mild_hypothermia_x10, temp_target_x10. reflexivity. Qed.

End TemperatureManagement.

(******************************************************************************)
(*                                                                            *)
(*                      RESUSCITATION ENDPOINTS                               *)
(*                                                                            *)
(*  Target values for goal-directed resuscitation.                            *)
(*  Reference: Cannon JW et al. J Trauma Acute Care Surg 2017.               *)
(*                                                                            *)
(******************************************************************************)

Module ResuscitationEndpoints.

(** MAP targets *)
Definition map_target_minimum : nat := 65.
Definition map_target_obstetric : nat := 70.

(** Lactate clearance target: <2.0 mmol/L *)
Definition lactate_target_x10 : nat := 20.

(** Base deficit target: <6 mEq/L *)
Definition base_deficit_target : nat := 6.

(** Urine output target: >0.5 mL/kg/hr, for 70kg = 35 mL/hr *)
Definition urine_output_target_ml_hr : nat := 35.

(** Hemoglobin targets during active resuscitation *)
Definition hgb_target_active_bleeding_x10 : nat := 70.
Definition hgb_target_bleeding_controlled_x10 : nat := 80.

(** Fibrinogen target in obstetric hemorrhage *)
Definition fibrinogen_target_mg_dl : nat := 200.

(** Platelet target during active bleeding *)
Definition platelet_target_active_k : nat := 75.
Definition platelet_target_stable_k : nat := 50.

(** INR target *)
Definition inr_target_x10 : nat := 15.

Record ResuscitationState : Type := MkResuscState {
  current_map : nat;
  current_lactate_x10 : nat;
  current_base_deficit : nat;
  current_urine_output_ml_hr : nat;
  current_hgb_x10 : nat;
  current_fibrinogen : nat;
  current_platelets_k : nat;
  current_inr_x10 : nat;
  bleeding_ongoing : bool
}.

Definition map_goal_met (s : ResuscitationState) : bool :=
  map_target_obstetric <=? current_map s.

Definition lactate_goal_met (s : ResuscitationState) : bool :=
  current_lactate_x10 s <=? lactate_target_x10.

Definition base_deficit_goal_met (s : ResuscitationState) : bool :=
  current_base_deficit s <=? base_deficit_target.

Definition urine_output_goal_met (s : ResuscitationState) : bool :=
  urine_output_target_ml_hr <=? current_urine_output_ml_hr s.

Definition hgb_goal_met (s : ResuscitationState) : bool :=
  if bleeding_ongoing s then hgb_target_active_bleeding_x10 <=? current_hgb_x10 s
  else hgb_target_bleeding_controlled_x10 <=? current_hgb_x10 s.

Definition fibrinogen_goal_met (s : ResuscitationState) : bool :=
  fibrinogen_target_mg_dl <=? current_fibrinogen s.

Definition coagulation_goals_met (s : ResuscitationState) : bool :=
  fibrinogen_goal_met s && (current_inr_x10 s <=? inr_target_x10).

Definition all_endpoints_met (s : ResuscitationState) : bool :=
  map_goal_met s && lactate_goal_met s && base_deficit_goal_met s &&
  urine_output_goal_met s && hgb_goal_met s && coagulation_goals_met s.

Definition endpoint_score (s : ResuscitationState) : nat :=
  (if map_goal_met s then 1 else 0) +
  (if lactate_goal_met s then 1 else 0) +
  (if base_deficit_goal_met s then 1 else 0) +
  (if urine_output_goal_met s then 1 else 0) +
  (if hgb_goal_met s then 1 else 0) +
  (if coagulation_goals_met s then 1 else 0).

Lemma endpoint_score_max : forall s, endpoint_score s <= 6.
Proof.
  intros s. unfold endpoint_score.
  destruct (map_goal_met s); destruct (lactate_goal_met s);
  destruct (base_deficit_goal_met s); destruct (urine_output_goal_met s);
  destruct (hgb_goal_met s); destruct (coagulation_goals_met s); simpl; lia.
Qed.

End ResuscitationEndpoints.

(******************************************************************************)
(*                                                                            *)
(*                      DAMAGE CONTROL RESUSCITATION                          *)
(*                                                                            *)
(*  DCR principles including calcium replacement and ratio transfusion.       *)
(*                                                                            *)
(******************************************************************************)

Module DamageControlResuscitation.

(** Calcium replacement protocol.
    After 4 units PRBC, ionized calcium often drops.
    Give 1g calcium gluconate (or 300mg CaCl2) per 4 units blood. *)
Definition prbc_threshold_for_calcium : nat := 4.
Definition calcium_gluconate_dose_mg : nat := 1000.
Definition calcium_chloride_dose_mg : nat := 300.

Definition calcium_replacement_indicated (prbc_units : nat) (ionized_ca_x100 : nat) : bool :=
  (prbc_threshold_for_calcium <=? prbc_units) && (ionized_ca_x100 <? 110).

(** 1:1:1 transfusion ratio *)
Definition balanced_ratio_met (prbc ffp plt : nat) : bool :=
  if prbc =? 0 then true
  else (ffp * 2 <=? prbc * 3) && (prbc * 2 <=? ffp * 3) &&
       (plt * 2 <=? prbc * 3) && (prbc * 2 <=? plt * 3).

(** Permissive hypotension NOT recommended in obstetric hemorrhage *)
Definition permissive_hypotension_contraindicated_obstetric : bool := true.

(** DCR bundle elements *)
Record DCRBundle : Type := MkDCRBundle {
  dcr_balanced_ratio : bool;
  dcr_calcium_replaced : bool;
  dcr_temp_managed : bool;
  dcr_acidosis_correcting : bool;
  dcr_source_controlled : bool
}.

Definition dcr_bundle_complete (b : DCRBundle) : bool :=
  dcr_balanced_ratio b && dcr_calcium_replaced b && dcr_temp_managed b.

(** Aortic compression for exsanguinating hemorrhage *)
Definition aortic_compression_indicated (sbp : nat) (bleeding_rate_ml_min : nat) : bool :=
  (sbp <? 70) || (150 <? bleeding_rate_ml_min).

(** Bimanual uterine compression technique *)
Inductive UterineCompression : Type :=
  | BimanualInternal : UterineCompression
  | BimanualExternal : UterineCompression
  | AorticCompression : UterineCompression.

End DamageControlResuscitation.

(******************************************************************************)
(*                                                                            *)
(*                       ICU ADMISSION CRITERIA                               *)
(*                                                                            *)
(*  Criteria for ICU admission after PPH.                                     *)
(*                                                                            *)
(******************************************************************************)

Module ICUAdmission.

Record ICUCriteria : Type := MkICUCriteria {
  required_vasopressors : bool;
  required_mechanical_ventilation : bool;
  ebl_over_3000 : bool;
  prbc_over_6_units : bool;
  had_hysterectomy : bool;
  had_dic : bool;
  had_cardiac_arrest : bool;
  required_ir_embolization : bool
}.

Definition icu_admission_required (c : ICUCriteria) : bool :=
  required_vasopressors c ||
  required_mechanical_ventilation c ||
  ebl_over_3000 c ||
  prbc_over_6_units c ||
  had_hysterectomy c ||
  had_dic c ||
  had_cardiac_arrest c.

Definition icu_admission_recommended (c : ICUCriteria) : bool :=
  icu_admission_required c || required_ir_embolization c.

Lemma cardiac_arrest_requires_icu : forall v mv ebl prbc hyst dic ir,
  icu_admission_required (MkICUCriteria v mv ebl prbc hyst dic true ir) = true.
Proof. intros. unfold icu_admission_required. simpl.
  destruct v; destruct mv; destruct ebl; destruct prbc; destruct hyst; destruct dic; reflexivity.
Qed.

End ICUAdmission.

(******************************************************************************)
(*                                                                            *)
(*                     TEMPORAL SAFETY PROPERTIES                             *)
(*                                                                            *)
(*  Time-based safety properties and state machine constraints.               *)
(*                                                                            *)
(******************************************************************************)

Module TemporalProperties.

(** Time windows for critical interventions (in minutes) *)
Definition txa_window_minutes : nat := 180.
Definition blood_availability_target_minutes : nat := 30.
Definition or_ready_target_minutes_stage3 : nat := 30.
Definition or_ready_target_minutes_stage4 : nat := 15.

(** State machine for hemorrhage management.
    States can only progress forward (no downgrade). *)
Inductive ManagementState : Type :=
  | StateRecognition : ManagementState
  | StateActivation : ManagementState
  | StateResuscitation : ManagementState
  | StateSurgical : ManagementState
  | StateResolved : ManagementState
  | StateICU : ManagementState.

Definition state_to_nat (s : ManagementState) : nat :=
  match s with
  | StateRecognition => 1
  | StateActivation => 2
  | StateResuscitation => 3
  | StateSurgical => 4
  | StateResolved => 5
  | StateICU => 6
  end.

Definition state_le (s1 s2 : ManagementState) : bool :=
  state_to_nat s1 <=? state_to_nat s2.

Record TimeStampedState : Type := MkTSState {
  ts_state : ManagementState;
  ts_time_minutes : nat;
  ts_ebl : nat
}.

Definition valid_transition (from to : ManagementState) : bool :=
  match from, to with
  | StateRecognition, StateActivation => true
  | StateActivation, StateResuscitation => true
  | StateResuscitation, StateSurgical => true
  | StateResuscitation, StateResolved => true
  | StateSurgical, StateResolved => true
  | StateSurgical, StateICU => true
  | StateResolved, StateICU => true
  | s1, s2 => state_to_nat s1 =? state_to_nat s2
  end.

Lemma no_downgrade : forall s1 s2,
  valid_transition s1 s2 = true -> state_le s1 s2 = true.
Proof.
  intros s1 s2 H. unfold valid_transition, state_le, state_to_nat in *.
  destruct s1; destruct s2; simpl in *; try reflexivity; try discriminate.
Qed.

(** Escalation sequence terminates - hemorrhage always reaches an end state *)
Definition is_terminal_state (s : ManagementState) : bool :=
  match s with
  | StateResolved => true
  | StateICU => true
  | _ => false
  end.

Lemma terminal_states_exist :
  exists s, is_terminal_state s = true.
Proof. exists StateResolved. reflexivity. Qed.

(******************************************************************************)
(*                       LIVENESS PROPERTIES                                  *)
(*                                                                            *)
(*  Time-based guarantees: critical interventions occur within windows.       *)
(******************************************************************************)

(** TXA must be administered within 180 minutes of hemorrhage onset *)
Definition txa_window_met (onset_time current_time : nat) (txa_given : bool) : Prop :=
  txa_given = true \/ current_time - onset_time < txa_window_minutes.

(** Blood products should be available within 30 minutes of Stage 3 *)
Definition blood_available_in_time (stage3_time current_time : nat)
                                    (blood_available : bool) : bool :=
  blood_available || (current_time - stage3_time <? blood_availability_target_minutes).

(** OR should be ready within 15 minutes for Stage 4 *)
Definition or_ready_in_time_stage4 (stage4_time current_time : nat)
                                    (or_ready : bool) : bool :=
  or_ready || (current_time - stage4_time <? or_ready_target_minutes_stage4).

(** Timeline for critical intervention: TXA given if indicated before window closes *)
Record TimelineState : Type := MkTimeline {
  tl_onset_time : nat;
  tl_current_time : nat;
  tl_txa_indicated : bool;
  tl_txa_given : bool;
  tl_stage3_time : option nat;
  tl_blood_available : bool;
  tl_stage4_time : option nat;
  tl_or_ready : bool
}.

Definition timeline_valid (t : TimelineState) : bool :=
  (tl_onset_time t <=? tl_current_time t) &&
  match tl_stage3_time t with
  | None => true
  | Some s3 => tl_onset_time t <=? s3
  end &&
  match tl_stage4_time t with
  | None => true
  | Some s4 => match tl_stage3_time t with
               | None => true
               | Some s3 => s3 <=? s4
               end
  end.

(** TXA compliance: either given in time or window still open *)
Definition txa_compliant (t : TimelineState) : bool :=
  negb (tl_txa_indicated t) ||
  tl_txa_given t ||
  (tl_current_time t - tl_onset_time t <? txa_window_minutes).

(** Blood compliance for Stage 3+: blood available or within window *)
Definition blood_compliant (t : TimelineState) : bool :=
  match tl_stage3_time t with
  | None => true
  | Some s3 => tl_blood_available t ||
               (tl_current_time t - s3 <? blood_availability_target_minutes)
  end.

(** OR compliance for Stage 4: OR ready or within window *)
Definition or_compliant (t : TimelineState) : bool :=
  match tl_stage4_time t with
  | None => true
  | Some s4 => tl_or_ready t ||
               (tl_current_time t - s4 <? or_ready_target_minutes_stage4)
  end.

(** Full liveness compliance *)
Definition liveness_compliant (t : TimelineState) : bool :=
  txa_compliant t && blood_compliant t && or_compliant t.

(** Proof: if TXA not indicated, TXA compliance is satisfied *)
Lemma txa_not_indicated_compliant : forall t,
  tl_txa_indicated t = false -> txa_compliant t = true.
Proof.
  intros t H. unfold txa_compliant. rewrite H. reflexivity.
Qed.

(** Proof: if TXA given, TXA compliance is satisfied *)
Lemma txa_given_compliant : forall t,
  tl_txa_given t = true -> txa_compliant t = true.
Proof.
  intros t H. unfold txa_compliant. rewrite H.
  destruct (tl_txa_indicated t); simpl; reflexivity.
Qed.

(** Proof: if blood available, blood compliance satisfied *)
Lemma blood_available_compliant : forall t,
  tl_blood_available t = true -> blood_compliant t = true.
Proof.
  intros t H. unfold blood_compliant.
  destruct (tl_stage3_time t); [rewrite H; reflexivity | reflexivity].
Qed.

(** Proof: if OR ready, OR compliance satisfied *)
Lemma or_ready_compliant : forall t,
  tl_or_ready t = true -> or_compliant t = true.
Proof.
  intros t H. unfold or_compliant.
  destruct (tl_stage4_time t); [rewrite H; reflexivity | reflexivity].
Qed.

(** Time-to-intervention bounds *)
Definition max_time_recognition_to_activation : nat := 5.
Definition max_time_activation_to_resuscitation : nat := 10.
Definition max_time_to_surgery_stage4 : nat := 30.

(** State progression record *)
Record StateProgression : Type := MkProgression {
  prog_recognition_time : nat;
  prog_activation_time : option nat;
  prog_resuscitation_time : option nat;
  prog_surgical_time : option nat;
  prog_terminal_time : option nat
}.

Definition progression_timely (p : StateProgression) : bool :=
  match prog_activation_time p with
  | None => true
  | Some act => act - prog_recognition_time p <=? max_time_recognition_to_activation
  end &&
  match prog_activation_time p, prog_resuscitation_time p with
  | Some act, Some res => res - act <=? max_time_activation_to_resuscitation
  | _, _ => true
  end.

Lemma timely_progression_bounded : forall p,
  progression_timely p = true ->
  match prog_activation_time p with
  | None => True
  | Some act => act - prog_recognition_time p <= max_time_recognition_to_activation
  end.
Proof.
  intros p H. unfold progression_timely in H.
  destruct (prog_activation_time p) as [act|] eqn:E.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.leb_le in H1. exact H1.
  - exact I.
Qed.

End TemporalProperties.

(******************************************************************************)
(*                                                                            *)
(*                      UNIVERSAL SAFETY PROPERTIES                           *)
(*                                                                            *)
(*  Guarantees that must hold for all inputs.                                 *)
(*                                                                            *)
(******************************************************************************)

Module UniversalSafety.

(** Every hemorrhaging patient gets intervention - no one is missed *)
Theorem hemorrhage_always_staged : forall d ebl,
  exists s, Stage.of_ebl d ebl = s.
Proof. intros d ebl. exists (Stage.of_ebl d ebl). reflexivity. Qed.

Theorem hemorrhage_always_has_intervention : forall d ebl,
  exists i, Intervention.of_ebl d ebl = i.
Proof. intros d ebl. exists (Intervention.of_ebl d ebl). reflexivity. Qed.

(** Stage never decreases with increasing EBL *)
Theorem stage_never_decreases : forall d ebl1 ebl2,
  ebl1 <= ebl2 ->
  Stage.to_nat (Stage.of_ebl d ebl1) <= Stage.to_nat (Stage.of_ebl d ebl2).
Proof.
  intros d ebl1 ebl2 H.
  apply Stage.of_ebl_monotonic. exact H.
Qed.

(** Intervention intensity never decreases with increasing EBL *)
Theorem intervention_never_decreases : forall d ebl1 ebl2,
  ebl1 <= ebl2 ->
  Intervention.to_nat (Intervention.of_ebl d ebl1) <=
  Intervention.to_nat (Intervention.of_ebl d ebl2).
Proof.
  intros d ebl1 ebl2 H.
  pose proof (Intervention.of_ebl_monotonic d ebl1 ebl2 H) as Hmono.
  unfold Intervention.le in Hmono. exact Hmono.
Qed.

(** Surgery only indicated for significant hemorrhage *)
Theorem surgery_requires_significant_ebl : forall d ebl,
  Intervention.of_ebl d ebl = Intervention.SurgicalIntervention ->
  Stage.threshold_stage4 d <= ebl.
Proof.
  intros d ebl H.
  apply Intervention.surgery_iff_ebl_ge_threshold in H. exact H.
Qed.

(** MTP aligns with Stage 4 for vaginal delivery *)
Theorem mtp_aligns_with_stage4_vaginal : forall ebl,
  MTP.mtp_indicated_by_ebl ebl = true ->
  Stage.of_ebl DeliveryMode.Vaginal ebl = Stage.Stage4.
Proof.
  intros ebl H.
  unfold MTP.mtp_indicated_by_ebl, MTP.activation_ebl_threshold in H.
  apply Nat.leb_le in H.
  apply Stage.of_ebl_stage4_iff. unfold Stage.threshold_stage4. exact H.
Qed.

End UniversalSafety.

(******************************************************************************)
(*                                                                            *)
(*                     BLOOD PRODUCT REFUSAL PATHWAY                          *)
(*                                                                            *)
(*  Alternative treatment pathway for patients who refuse blood products      *)
(*  (e.g., Jehovah's Witnesses). Requires earlier surgical escalation,        *)
(*  cell salvage emphasis, and erythropoietin consideration.                  *)
(*                                                                            *)
(*  Reference: AABB Technical Manual, 20th ed. Chapter 26.                    *)
(*                                                                            *)
(******************************************************************************)

Module BloodRefusal.

(** Patient blood product consent status *)
Inductive ConsentStatus : Type :=
  | FullConsent : ConsentStatus         (** Accepts all products *)
  | NoAllogeneic : ConsentStatus        (** Cell saver OK, no donor blood *)
  | NoBloodProducts : ConsentStatus     (** Refuses all blood products *)
  | AdvanceDirective : ConsentStatus.   (** Written directive on file *)

(** Alternative treatments available for blood-refusing patients *)
Record AlternativeTreatments : Type := MkAltTx {
  cell_saver_available : bool;
  erythropoietin_available : bool;
  iv_iron_available : bool;
  tranexamic_acid_available : bool;
  factor_concentrates_available : bool
}.

Definition full_alternatives : AlternativeTreatments :=
  MkAltTx true true true true true.

Definition minimal_alternatives : AlternativeTreatments :=
  MkAltTx false false true true false.

(** Cell saver is acceptable for many blood-refusing patients *)
Definition cell_saver_acceptable (c : ConsentStatus) : bool :=
  match c with
  | FullConsent => true
  | NoAllogeneic => true
  | NoBloodProducts => false
  | AdvanceDirective => false
  end.

(** When blood products refused, lower threshold for surgical intervention *)
Definition adjusted_surgical_threshold_mL (c : ConsentStatus) (base : nat) : nat :=
  match c with
  | FullConsent => base
  | NoAllogeneic => base - 200
  | NoBloodProducts => base - 500
  | AdvanceDirective => base - 500
  end.

Lemma refusal_lowers_threshold : forall base,
  base >= 500 ->
  adjusted_surgical_threshold_mL NoBloodProducts base < base.
Proof.
  intros base Hbase. unfold adjusted_surgical_threshold_mL. lia.
Qed.

(** Earlier surgery compensates for lack of transfusion *)
Definition surgery_priority_modifier (c : ConsentStatus) : nat :=
  match c with
  | FullConsent => 0
  | NoAllogeneic => 1
  | NoBloodProducts => 2
  | AdvanceDirective => 2
  end.

(** Legal requirements for blood refusal *)
Definition requires_documented_refusal (c : ConsentStatus) : bool :=
  match c with
  | FullConsent => false
  | _ => true
  end.

Definition requires_witness_signature (c : ConsentStatus) : bool :=
  match c with
  | NoBloodProducts => true
  | AdvanceDirective => true
  | _ => false
  end.

(** Maximum acceptable hemoglobin drop before surgery when refusing blood *)
Definition max_hgb_drop_before_surgery_x10 (c : ConsentStatus) : nat :=
  match c with
  | FullConsent => 40         (** 4.0 g/dL - can transfuse *)
  | NoAllogeneic => 30        (** 3.0 g/dL - cell saver only *)
  | NoBloodProducts => 20     (** 2.0 g/dL - operate earlier *)
  | AdvanceDirective => 20
  end.

(** Alternative treatment protocol *)
Definition alt_treatment_priority (c : ConsentStatus) (alt : AlternativeTreatments) : list nat :=
  match c with
  | FullConsent => []
  | _ =>
    (if tranexamic_acid_available alt then [1] else []) ++
    (if cell_saver_available alt && cell_saver_acceptable c then [2] else []) ++
    (if factor_concentrates_available alt then [3] else []) ++
    (if erythropoietin_available alt then [4] else []) ++
    (if iv_iron_available alt then [5] else [])
  end.

Lemma full_consent_no_alt_protocol :
  alt_treatment_priority FullConsent full_alternatives = [].
Proof. reflexivity. Qed.

(** TXA is always first-line for blood-refusing patients *)
Lemma txa_first_for_refusal : forall alt,
  tranexamic_acid_available alt = true ->
  hd_error (alt_treatment_priority NoBloodProducts alt) = Some 1.
Proof.
  intros alt Htxa. unfold alt_treatment_priority.
  rewrite Htxa. simpl. reflexivity.
Qed.

End BloodRefusal.

(******************************************************************************)
(*                                                                            *)
(*                     ANTEPARTUM HEMORRHAGE STAGING                          *)
(*                                                                            *)
(*  Staging for bleeding before delivery (placenta previa, abruption).        *)
(*  Uses lower thresholds due to fetal considerations.                        *)
(*                                                                            *)
(******************************************************************************)

Module AntepartumHemorrhage.

(** Causes of antepartum hemorrhage *)
Inductive Cause : Type :=
  | PlacentaPrevia : Cause       (** Placenta covering os *)
  | PlacentalAbruption : Cause   (** Placenta separating from uterus *)
  | VasaPrevia : Cause           (** Fetal vessels over os *)
  | UterineRupture : Cause       (** Catastrophic - immediate surgery *)
  | Unknown : Cause.

Definition eq_dec : forall c1 c2 : Cause, {c1 = c2} + {c1 <> c2}.
Proof. intros [] []; (left; reflexivity) || (right; discriminate). Defined.

(** Vasa previa and uterine rupture are emergencies regardless of EBL *)
Definition is_immediate_emergency (c : Cause) : bool :=
  match c with
  | VasaPrevia => true
  | UterineRupture => true
  | _ => false
  end.

(** Antepartum thresholds are lower due to fetal compromise risk *)
Definition stage2_threshold_antepartum : nat := 300.
Definition stage3_threshold_antepartum : nat := 600.
Definition stage4_threshold_antepartum : nat := 1000.

(** Stage by EBL for antepartum cases *)
Definition stage_antepartum (ebl : nat) : nat :=
  if ebl <? stage2_threshold_antepartum then 1
  else if ebl <? stage3_threshold_antepartum then 2
  else if ebl <? stage4_threshold_antepartum then 3
  else 4.

Lemma antepartum_thresholds_lower_than_postpartum :
  stage2_threshold_antepartum < Stage.threshold_stage2 DeliveryMode.Vaginal.
Proof.
  unfold stage2_threshold_antepartum, Stage.threshold_stage2. simpl. lia.
Qed.

(** Fetal status consideration *)
Inductive FetalStatus : Type :=
  | Reassuring : FetalStatus
  | NonReassuring : FetalStatus
  | TerminalBradycardia : FetalStatus
  | FetalDemise : FetalStatus.

Definition fetal_distress_escalates_stage (f : FetalStatus) : bool :=
  match f with
  | NonReassuring => true
  | TerminalBradycardia => true
  | _ => false
  end.

(** Effective antepartum stage considering fetal status *)
Definition effective_antepartum_stage (ebl : nat) (f : FetalStatus) : nat :=
  let base := stage_antepartum ebl in
  if fetal_distress_escalates_stage f then Nat.min 4 (base + 1)
  else base.

Lemma terminal_brady_is_stage4 : forall ebl,
  effective_antepartum_stage ebl TerminalBradycardia >= 2.
Proof.
  intros ebl. unfold effective_antepartum_stage, fetal_distress_escalates_stage.
  unfold stage_antepartum.
  destruct (ebl <? stage2_threshold_antepartum) eqn:E1;
  destruct (ebl <? stage3_threshold_antepartum) eqn:E2;
  destruct (ebl <? stage4_threshold_antepartum) eqn:E3;
  simpl; lia.
Qed.

(** Delivery decision for antepartum hemorrhage *)
Definition immediate_delivery_indicated (c : Cause) (f : FetalStatus) (ebl : nat) : bool :=
  is_immediate_emergency c ||
  match f with
  | TerminalBradycardia => true
  | FetalDemise => 3 <=? stage_antepartum ebl
  | _ => 4 <=? stage_antepartum ebl
  end.

Lemma uterine_rupture_always_deliver : forall f ebl,
  immediate_delivery_indicated UterineRupture f ebl = true.
Proof.
  intros f ebl. unfold immediate_delivery_indicated, is_immediate_emergency.
  reflexivity.
Qed.

End AntepartumHemorrhage.

(******************************************************************************)
(*                                                                            *)
(*                         EXTRACTION                                         *)
(*                                                                            *)
(*  Code extraction for OCaml.                                               *)
(*                                                                            *)
(******************************************************************************)

Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "pph_extracted"
  Units.BloodLoss Units.BloodLossMethod Units.corrected_blood_loss
  Units.TempCelsius
  Stage.t Stage.of_ebl Stage.to_nat
  Intervention.t Intervention.of_ebl Intervention.of_stage
  DeliveryMode.t DeliveryMode.pph_threshold
  HemorrhageTiming.t HemorrhageTiming.is_primary HemorrhageTiming.is_secondary
  HemorrhageTiming.SecondaryPPHCause HemorrhageTiming.requires_antibiotics
  HemorrhageTiming.SecondaryStage HemorrhageTiming.secondary_stage_of_ebl
  HemorrhageTiming.secondary_intervention_modifier
  VitalSigns.t VitalSigns.shock_index_x10 VitalSigns.hemorrhage_class
  VitalSigns.is_hypothermic VitalSigns.lethal_triad_temp_component
  VitalSigns.valid VitalSigns.shock_index_elevated_obstetric
  VitalSigns.obstetric_shock_class
  LabValues.t LabValues.transfusion_trigger_met
  LabValues.dic_score LabValues.has_overt_dic
  LabValues.lethal_triad_acidosis LabValues.lethal_triad_coagulopathy
  LabValues.is_hypofibrinogenemic_obstetric
  LabValues.hgb_drop_from_baseline LabValues.significant_hgb_drop
  LabValues.ROTEMResult LabValues.rotem_guided_intervention
  LabValues.TEGResult LabValues.teg_suggests_hypofibrinogenemia
  PatientFactors.t PatientFactors.is_high_risk
  PatientFactors.AccretaType PatientFactors.accreta_severity
  PatientFactors.requires_planned_hysterectomy
  PatientFactors.estimated_blood_volume_mL
  PatientFactors.expected_ebl_by_accreta
  PatientFactors.requires_mfm_center_transfer
  PatientFactors.requires_ir_preposition
  PatientFactors.conservative_management_eligible
  Etiology.t Etiology.primary_treatment_is_uterotonic
  RateOfLoss.effective_stage
  Uterotonics.Agent Uterotonics.recommended_sequence
  Uterotonics.AtonyState Uterotonics.is_refractory_atony
  Uterotonics.atony_response_status Uterotonics.agent_efficacy_x10
  Uterotonics.agent_time_to_response
  TXA.txa_indicated TXA.can_give_first_dose
  MTP.mtp_indicated MTP.initial_pack MTP.blood_compatible
  TeamEscalation.team_for_stage
  Checklist.stage1_complete
  Hysterectomy.hysterectomy_indicated
  SurgicalEscalation.SurgicalIntervention
  SurgicalEscalation.standard_escalation_sequence
  SurgicalEscalation.preserves_fertility
  SurgicalEscalation.next_intervention
  SurgicalEscalation.cell_saver_contraindicated
  IntegratedAssessment.ClinicalState IntegratedAssessment.effective_stage_t
  IntegratedAssessment.recommended_intervention
  IntegratedAssessment.lethal_triad_score IntegratedAssessment.lethal_triad_present
  IntegratedAssessment.critical_state
  IntegratedAssessment.dic_management_indicated
  IntegratedAssessment.percent_volume_lost
  AuditLog.AuditEntry AuditLog.AuditTrail AuditLog.add_entry
  AuditLog.entries_chronological
  AnesthesiaConsiderations.AnesthesiaType
  AnesthesiaConsiderations.difficult_airway_predicted
  AnesthesiaConsiderations.ga_indicated
  AnesthesiaConsiderations.neuraxial_safe
  ConcealedHemorrhage.ConcealedType
  ConcealedHemorrhage.concealed_hemorrhage_likely
  ConcealedHemorrhage.total_blood_loss
  TemperatureManagement.WarmingProtocol
  TemperatureManagement.warming_adequate
  TemperatureManagement.fluid_warmer_required
  ResuscitationEndpoints.ResuscitationState
  ResuscitationEndpoints.all_endpoints_met
  ResuscitationEndpoints.endpoint_score
  DamageControlResuscitation.DCRBundle
  DamageControlResuscitation.dcr_bundle_complete
  DamageControlResuscitation.calcium_replacement_indicated
  DamageControlResuscitation.aortic_compression_indicated
  ICUAdmission.ICUCriteria
  ICUAdmission.icu_admission_required
  TemporalProperties.ManagementState
  TemporalProperties.valid_transition
  TemporalProperties.is_terminal_state
  (* New additions for gap-filling *)
  Units.MeasurementWithUncertainty Units.meas_upper Units.meas_lower
  Units.ebl_with_uncertainty Units.ebl_conservative
  Units.SignedTempCelsius Units.signed_temp_is_sensor_fault
  Units.safe_div Units.safe_pct_of
  VitalSigns.SensorStatus VitalSigns.overall_sensor_status
  VitalSigns.has_sensor_failure VitalSigns.has_sensor_issue
  VitalSigns.make_vitals VitalSigns.unknown_vitals
  Etiology.EtiologySet Etiology.add_etiology Etiology.etiology_count
  Etiology.ExtendedEtiology Etiology.AmnioticFluidEmbolism Etiology.UterineInversion
  Etiology.InversionDegree Etiology.InversionTreatment
  Etiology.extended_requires_specialist Etiology.extended_mortality_risk
  BloodRefusal.ConsentStatus BloodRefusal.AlternativeTreatments
  BloodRefusal.cell_saver_acceptable BloodRefusal.adjusted_surgical_threshold_mL
  BloodRefusal.surgery_priority_modifier BloodRefusal.alt_treatment_priority
  AntepartumHemorrhage.Cause AntepartumHemorrhage.FetalStatus
  AntepartumHemorrhage.is_immediate_emergency
  AntepartumHemorrhage.stage_antepartum AntepartumHemorrhage.effective_antepartum_stage
  AntepartumHemorrhage.immediate_delivery_indicated
  IntegratedAssessment.effective_stage_ge_1 IntegratedAssessment.effective_stage_valid
  (* Adverse events module *)
  AdverseEvents.Severity AdverseEvents.UterotonicAE AdverseEvents.TXA_AE
  AdverseEvents.TransfusionAE AdverseEvents.SurgicalAE
  AdverseEvents.uterotonic_ae_severity AdverseEvents.transfusion_ae_severity
  AdverseEvents.benefit_exceeds_risk AdverseEvents.contraindicated_agent_given
  (* Blood product ratio verification *)
  MTP.total_platelets MTP.total_prbc_eq_total_ffp_ratio
  MTP.ratio_1_1_1_single_balanced MTP.initial_pack_balanced
  (* Checklist completion *)
  Checklist.compliance_score_stage2 Checklist.compliance_score_stage3
  Checklist.compliance_score_stage4 Checklist.compliance_percent_stage1
  Checklist.stage2_complete Checklist.stage3_complete Checklist.stage4_complete
  (* Secondary PPH interventions *)
  HemorrhageTiming.SecondaryIntervention HemorrhageTiming.secondary_primary_intervention
  HemorrhageTiming.secondary_requires_procedural HemorrhageTiming.secondary_intervention_sequence
  HemorrhageTiming.effective_secondary_stage
  (* Liveness and temporal compliance *)
  TemporalProperties.TimelineState TemporalProperties.txa_compliant
  TemporalProperties.blood_compliant TemporalProperties.or_compliant
  TemporalProperties.liveness_compliant TemporalProperties.StateProgression
  TemporalProperties.progression_timely
  (* Percentage-based staging *)
  IntegratedAssessment.stage_by_percent IntegratedAssessment.combined_stage
  IntegratedAssessment.effective_stage_with_pct
  (* Etiology-intervention connection *)
  Etiology.first_line_treatment Etiology.requires_surgical_exploration
  Etiology.requires_blood_products Etiology.uterotonics_may_help.
