/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Singmaster.Certified
import Singmaster.Fibonacci

/-!
# Exact multiplicities of the known repeated numbers

Besides `3003`, which appears eight times (`Singmaster.N3003`), every number known to appear
more than four times in Pascal's triangle is one of `120, 210, 1540, 7140, 11628, 24310`, or a
Lind–Singmaster number `C(F(2i+2) F(2i+3), F(2i) F(2i+3))` with `i ≥ 2`. The certificates of
`Singmaster.Certified` show that each of the six small numbers appears exactly six times, and
so do the Lind–Singmaster numbers for `i = 2` (`C(104, 39)`, 29 digits) and `i = 3`
(`C(714, 272)`, 205 digits).

Each certificate lists, for every column `k = 2, …, K - 1`, the largest row `a` with
`C(a, k) < t`. The kernel checks them with `decide +kernel`. They were produced by
`scripts/certificates.py`, which is not trusted: a wrong certificate fails the check.
-/

open Nat

namespace Singmaster

/-- `120 = C(16, 2) = C(10, 3)` appears exactly six times in Pascal's triangle. -/
theorem ncard_120 : (solutions 120).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(16, 2), (10, 3)]) (as := [15, 9, 8])
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- `210 = C(21, 2) = C(10, 4)` appears exactly six times in Pascal's triangle. -/
theorem ncard_210 : (solutions 210).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(21, 2), (10, 4)]) (as := [20, 11, 9])
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- `1540 = C(56, 2) = C(22, 3)` appears exactly six times in Pascal's triangle. -/
theorem ncard_1540 : (solutions 1540).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(56, 2), (22, 3)]) (as := [55, 21, 15, 13, 12])
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- `7140 = C(120, 2) = C(36, 3)` appears exactly six times in Pascal's triangle. -/
theorem ncard_7140 : (solutions 7140).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(120, 2), (36, 3)]) (as := [119, 35, 21, 17, 15, 15])
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- `11628 = C(153, 2) = C(19, 5)` appears exactly six times in Pascal's triangle. -/
theorem ncard_11628 : (solutions 11628).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(153, 2), (19, 5)]) (as := [152, 42, 24, 18, 16, 16])
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- `24310 = C(221, 2) = C(17, 8)` appears exactly six times in Pascal's triangle. -/
theorem ncard_24310 : (solutions 24310).ncard = 6 :=
  (ncard_eq_of_certOK (S := [(221, 2), (17, 8)]) (as := [220, 53, 29, 21, 18, 17, 16])
    (by norm_num) (by decide +kernel)).trans (by decide)

theorem choose_104_39 : (104 : ℕ).choose 39 =
    61218182743304701891431482520 :=
  (Nat.choose_eq_descFactorial_div_factorial 104 39).trans (by decide +kernel)

/-- Column certificates for `C(104, 39)`, columns `k = 2, …, 49`. -/
def cert_104_39 : List ℕ :=
  [349909081743543, 7161608258, 34815524, 1490091, 187949, 43788, 14933, 6554, 3429, 2037, 1330,
   934, 694, 540, 435, 362, 308, 268, 237, 213, 194, 179, 166, 156, 147, 140, 134, 129, 124, 120,
   117, 114, 112, 109, 108, 106, 105, 103, 102, 102, 101, 100, 100, 99, 99, 99, 99, 99]

/-- The Lind–Singmaster number for `i = 2`, `C(104, 39) = C(103, 40)` (29 digits),
appears exactly six times in Pascal's triangle. -/
theorem ncard_choose_104_39 : (solutions ((104 : ℕ).choose 39)).ncard = 6 := by
  rw [choose_104_39]
  exact (ncard_eq_of_certOK (S := [(104, 39), (103, 40)]) (as := cert_104_39)
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- The same statement in the form of `Singmaster.choose_fib_eq` with `i = 2`. -/
theorem ncard_solutions_fib_2 :
    (solutions ((fib 6 * fib 7).choose (fib 4 * fib 7))).ncard = 6 := by
  have h1 : fib 6 * fib 7 = 104 := by decide
  have h2 : fib 4 * fib 7 = 39 := by decide
  rw [h1, h2]
  exact ncard_choose_104_39

theorem choose_714_272 : (714 : ℕ).choose 272 =
    3537835171522765057006983148520718494957187357011427136691375227388082606684583032666088334962061461901090477513197821330000906170565587040820236444389470701575515092325417606033095416151914090271577807800 :=
  (Nat.choose_eq_descFactorial_div_factorial 714 272).trans (by decide +kernel)

/-- Column certificates for `C(714, 272)`, columns `k = 2, …, 342`. -/
def cert_714_272 : List ℕ :=
  [
   2660013222344116490616366969684053851145714423868164415842164657275050620380287908503238545446446966132,
   276882993626660541144073972619285615286764902355698144330064774109739,
   3035548731252726412718061340701925856635933921433525, 211633185139330292772919692364831233441057,
   36955437544665516404087720709065237, 562557444150543362198921591289, 139406256389340090335625276,
   221507766818076803240184, 1290773565947684020586, 19335434576236165877, 587610498671350470,
   30755617760834387, 2466504166222568, 278194889141510, 41384224781446, 7730790224897,
   1745616394079, 462315588875, 140198417211, 47742883276, 17968959004, 7376997798, 3267584326,
   1547302881, 777234705, 411420524, 228200773, 131985681, 79264733, 49246964, 31552126, 20787441,
   14048025, 9716597, 6865111, 4946040, 3627996, 2705625, 2048866, 1573664, 1224664, 964773, 768722,
   619036, 503455, 413260, 342177, 285633, 240259, 203548, 173616, 149031, 128698, 111771, 97593,
   85646, 75525, 66904, 59524, 53177, 47692, 42932, 38785, 35157, 31970, 29162, 26679, 24476, 22515,
   20764, 19197, 17790, 16523, 15380, 14345, 13407, 12554, 11777, 11068, 10420, 9825, 9279, 8777,
   8314, 7887, 7492, 7126, 6786, 6471, 6178, 5905, 5650, 5412, 5189, 4981, 4785, 4602, 4430, 4268,
   4115, 3972, 3836, 3708, 3587, 3472, 3364, 3261, 3163, 3071, 2983, 2899, 2820, 2744, 2672, 2603,
   2538, 2475, 2415, 2358, 2303, 2251, 2200, 2152, 2106, 2062, 2020, 1979, 1940, 1902, 1866, 1831,
   1798, 1766, 1734, 1705, 1676, 1648, 1621, 1595, 1570, 1546, 1522, 1500, 1478, 1457, 1436, 1417,
   1398, 1379, 1361, 1344, 1327, 1310, 1294, 1279, 1264, 1250, 1236, 1222, 1209, 1196, 1183, 1171,
   1159, 1148, 1136, 1125, 1115, 1104, 1094, 1085, 1075, 1066, 1057, 1048, 1039, 1031, 1023, 1015,
   1007, 999, 992, 985, 978, 971, 964, 958, 951, 945, 939, 933, 927, 922, 916, 911, 906, 900, 895,
   890, 886, 881, 876, 872, 867, 863, 859, 855, 851, 847, 843, 839, 835, 832, 828, 825, 821, 818,
   815, 812, 809, 806, 803, 800, 797, 794, 791, 789, 786, 784, 781, 779, 776, 774, 772, 769, 767,
   765, 763, 761, 759, 757, 755, 753, 751, 749, 747, 746, 744, 742, 741, 739, 738, 736, 735, 733,
   732, 730, 729, 727, 726, 725, 724, 722, 721, 720, 719, 718, 717, 716, 715, 713, 712, 712, 711,
   710, 709, 708, 707, 706, 705, 705, 704, 703, 702, 701, 701, 700, 699, 699, 698, 698, 697, 696,
   696, 695, 695, 694, 694, 693, 693, 692, 692, 691, 691, 691, 690, 690, 689, 689, 689, 688, 688,
   688, 688, 687, 687, 687, 687, 686, 686, 686, 686, 686, 685, 685, 685, 685, 685, 685, 685, 684,
   684, 684, 684, 684, 684, 684, 684, 684, 684, 684]

/-- The Lind–Singmaster number for `i = 3`, `C(714, 272) = C(713, 273)` (205 digits),
appears exactly six times in Pascal's triangle. -/
theorem ncard_choose_714_272 : (solutions ((714 : ℕ).choose 272)).ncard = 6 := by
  rw [choose_714_272]
  exact (ncard_eq_of_certOK (S := [(714, 272), (713, 273)]) (as := cert_714_272)
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- The same statement in the form of `Singmaster.choose_fib_eq` with `i = 3`. -/
theorem ncard_solutions_fib_3 :
    (solutions ((fib 8 * fib 9).choose (fib 6 * fib 9))).ncard = 6 := by
  have h1 : fib 8 * fib 9 = 714 := by decide
  have h2 : fib 6 * fib 9 = 272 := by decide
  rw [h1, h2]
  exact ncard_choose_714_272

end Singmaster
