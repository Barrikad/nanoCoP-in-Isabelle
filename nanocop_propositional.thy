theory nanocop_propositional imports Main
begin

(*--List Set Operations----*)
primrec member (infix\<open>|\<in>|\<close> 200) where
  \<open>(_ |\<in>| []) = False\<close> |
  \<open>(x |\<in>| (x' # xs)) = ((x = x') \<or> (x |\<in>| xs))\<close>

lemma member_simp[simp]: \<open>x |\<in>| xs \<longleftrightarrow> x \<in> (set xs)\<close> 
  by (induct xs) simp_all

abbreviation notmember (infix \<open>|\<notin>|\<close> 200) where \<open>x |\<notin>| xs \<equiv> \<not> x |\<in>| xs\<close>

definition \<open>linsert x xs \<equiv> (if (x |\<in>| xs) then xs else x # xs)\<close>

lemma linsert_is_insert: \<open>set (linsert x xs) = insert x (set xs)\<close>
  by (induct xs) (simp_all add: linsert_def insert_absorb)

primrec subseteq (infix \<open>|\<subseteq>|\<close> 120) where
  \<open>([] |\<subseteq>| _) = True\<close> |
  \<open>((x # xs) |\<subseteq>| ys) = ((x |\<in>| ys) \<and> (xs |\<subseteq>| ys))\<close>

lemma subseteq_simp[simp]: \<open>xs |\<subseteq>| ys \<longleftrightarrow> (set xs) \<subseteq> (set ys)\<close> 
  by (induct xs) simp_all

primrec lremove where
  \<open>lremove _ [] = []\<close> |
  \<open>lremove x (y # ys) = (if y = x then lremove x ys else y # (lremove x ys))\<close>

lemma lremove_simp[simp]: \<open>set (lremove x xs) = (set xs) - {x}\<close>
  by (induct xs) (simp_all add: insert_Diff_if)
  
primrec lminus (infix \<open>|-|\<close> 210) where
  \<open>xs |-| [] = xs\<close> |
  \<open>xs |-| (y # ys) = (lremove y xs) |-| ys\<close>

lemma hoist_lremove:\<open>set ((lremove x xs) |-| ys) = set (lremove x (xs |-| ys))\<close> 
  apply (induct ys arbitrary: x xs)
   apply simp
  by (metis Diff_insert Diff_insert2 lminus.simps(2) lremove_simp)

lemma lminus_simp[simp]: \<open>set (xs |-| ys) = (set xs) - (set ys)\<close>
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  have \<open>set (xs |-| (y # ys)) = set (xs |-| ys) - {y}\<close>
    by (simp add: hoist_lremove)
  then show ?case
    using Cons.hyps by force
qed

definition lequal (infix \<open>|=|\<close> 120) where \<open>xs |=| ys \<equiv> xs |\<subseteq>| ys \<and> ys |\<subseteq>| xs\<close>

lemma lequal_simp[simp]: \<open>xs |=| ys \<longleftrightarrow> (set xs) = (set ys)\<close>
  by (simp add: lequal_def set_eq_subset)

primrec lunion (infix \<open>|\<union>|\<close> 110) where
  \<open>lunion xs [] = xs\<close> |
  \<open>lunion xs (y # ys) = (if y |\<in>| xs then lunion xs ys else y # (lunion xs ys))\<close>

lemma lunion_simp[simp]: \<open>set (xs |\<union>| ys) = set xs \<union> set ys\<close> 
  by (induct ys) auto

primrec isset where
  \<open>isset [] = True\<close> |
  \<open>isset (x # xs) = (x |\<notin>| xs \<and> isset xs)\<close>

lemma isset_length: \<open>isset xs \<Longrightarrow> size xs = size (sorted_list_of_set (set xs))\<close>
  by (induct xs) simp_all

primrec union_many where
  \<open>union_many [] = {}\<close> |
  \<open>union_many (xs # ys) = xs \<union> (union_many ys)\<close>


fun count where
  \<open>count x [] = 0\<close> |
  \<open>count x (y # ys) = (if x = y then Suc (count x ys) else count x ys)\<close>

lemma count_0: \<open>count x xs = 0 \<longleftrightarrow> x \<notin> set xs\<close>
  by (induct xs) auto

lemma count_1: \<open>count x ys \<ge> 1 \<longleftrightarrow> x \<in> set ys\<close>
  by (induct ys) (simp_all | force)

fun remove where
  \<open>remove x [] = []\<close> |
  \<open>remove x (y # ys) = (
    if x = y 
    then ys
    else y # remove x ys)\<close>

lemma remove_length: \<open>member x ys \<Longrightarrow> length ys = length (remove x ys) + 1\<close> 
  by (induct ys) auto

lemma remove_set: \<open>member x ys \<Longrightarrow> set ([x] |\<union>| (remove x ys)) = set ys\<close> 
  by (induct ys) (auto|force)

lemma remove_count: \<open>member x ys \<Longrightarrow> count x ys = count x (remove x ys) + 1\<close>
  by (induct ys) auto

lemma remove_count2: \<open>x \<noteq> y \<Longrightarrow> count x ys = count x (remove y ys)\<close> 
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons z ys)
  consider (1)\<open>z = y\<close> | (2)\<open>z \<noteq> y\<close> by fast
  then show ?case
  proof cases
    case 1
    then have \<open>count x (remove y (z # ys)) = count x ys\<close> 
      by simp
    moreover have \<open>x \<noteq> z \<Longrightarrow> count x ys = count x (z # ys)\<close> 
      by simp
    ultimately show ?thesis 
      by (metis "1" Cons.prems)
  next
    case 2
    show ?thesis 
        using Cons.hyps Cons.prems by auto
  qed
qed

fun permutation where
  \<open>permutation [] [] = True\<close> |
  \<open>permutation _ [] = False\<close> |
  \<open>permutation [] _ = False\<close> |
  \<open>permutation (x # xs) ys = (
    member x ys \<and>
    permutation xs (remove x ys))\<close>

lemma permutation_count: \<open>permutation xs ys \<longleftrightarrow> (\<forall> x. count x xs = count x ys)\<close>
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by 
      (metis count.simps(1) count_0 list.set_intros(1) neq_Nil_conv permutation.simps(1) 
        permutation.simps(3))
next
  case (Cons x xs)
  have rimp: \<open>permutation (x # xs) ys \<Longrightarrow> (\<forall> y. count y (x # xs) = count y ys)\<close> 
  proof
    fix y
    assume asm:\<open>permutation (x # xs) ys\<close>
    consider (1) \<open>x = y\<close> | (2) \<open>x \<noteq> y\<close> by fast
    then show \<open>count y (x # xs) = count y ys\<close> 
    proof cases
      case 1
      have \<open>member x ys\<close> 
        using asm permutation.elims(2) by blast
      then have \<open>count x ys = count x (remove x ys) + 1\<close> 
        by (simp add: remove_count)
      then show ?thesis 
        using 1 asm local.Cons permutation.elims(2) permutation.simps(4) remove.simps(2) 
        by fastforce
    next
      case 2
      then have \<open>count y ys = count y (remove x ys)\<close> sorry
      moreover have \<open>count y xs = count y (x # xs)\<close> using 2 by auto
      ultimately show ?thesis using asm
        by (smt (verit, ccfv_threshold) list.inject local.Cons permutation.elims(2))
    qed
  qed
  have limp: \<open>(\<forall> y. count y (x # xs) = count y ys) \<Longrightarrow> permutation (x # xs) ys\<close>
  proof-
    assume \<open>(\<forall> y. count y (x # xs) = count y ys)\<close>
    show \<open>permutation (x # xs) ys\<close> sorry
  qed
  then show ?case using limp rimp by fast
qed 
  
lemma permutation_alt: \<open>permutation xs ys \<Longrightarrow> length xs = length ys \<and> set xs = set ys\<close>
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case using permutation.elims(2) by auto
next
  case (Cons x xs)
  have \<open>member x ys\<close> 
    using Cons.prems permutation.elims(2) by blast
  then have \<open>length (x # xs) = length ys\<close>
    using remove_length 
    by (smt (verit, ccfv_threshold) Cons.hyps Cons.prems list.inject 
        member.simps(2) permutation.elims(2) remove.simps(2))
  moreover have \<open>member x xs \<Longrightarrow> set (x # xs) = set ys\<close>
    by (smt (verit) Cons.hyps Cons.prems insert_absorb list.inject list.simps(15) lunion_simp 
        member_simp permutation.elims(2) remove_set sup.left_idem)
  ultimately show ?case sorry
qed
  
(*-------------------------*)


(*--------NaNoCop----------*)
datatype mat 
  = Lit bool nat
  | Mat \<open>(nat \<times> (nat \<times> mat) list) list\<close>


fun exi_clause where
  \<open>exi_clause P (_,Lit _ _) = False\<close> |
  \<open>exi_clause P (_,Mat []) = False\<close> |
  \<open>exi_clause P (mid,Mat ((cid,ms) # cs)) = 
  (P (cid,ms) \<or> (\<exists> m \<in> set ms. exi_clause P m) \<or> exi_clause P (mid,Mat cs))\<close>

definition \<open>exi_mat P m \<equiv> P m \<or> exi_clause (\<lambda> (_,ms). \<exists> m' \<in> set ms. P m') m\<close>

fun all_clause where
  \<open>all_clause P (_,Lit _ _) = True\<close> |
  \<open>all_clause P (_,Mat []) = True\<close> |
  \<open>all_clause P (mid,Mat ((cid,ms) # cs)) = 
  (P (cid,ms) \<and> (\<forall> m \<in> set ms. all_clause P m) \<and> all_clause P (mid,Mat cs))\<close>

definition \<open>all_mat P m \<equiv> P m \<and> all_clause (\<lambda> (_,ms). \<forall> m' \<in> set ms. P m') m\<close>

definition \<open>contains_cls c m \<equiv> exi_clause (\<lambda> c'. c = c') m\<close>

definition \<open>contains_mat m1 m2 \<equiv> exi_mat (\<lambda> m'. m' = m1) m2\<close>

definition \<open>id_exists idty m \<equiv> exi_clause (\<lambda> (n,_). n = idty) m \<or> exi_mat (\<lambda> (n,_). n = idty) m\<close>

fun siblings where
  \<open>siblings c1 c2 (_,Lit _ _) = False\<close> |
  \<open>siblings c1 c2 (_,Mat cs) = (member c1 cs \<and> member c2 cs)\<close>

abbreviation \<open>
  alpha_top_level c l m \<equiv> (\<exists> cid' c'. 
    c \<noteq> (cid',c') \<and> 
    siblings c (cid',c') m \<and> 
    (\<exists> m' \<in> set c'. contains_mat l m'))\<close>

definition \<open>extension_clause M P C \<equiv> True\<close>

(*fun beta_clause where
  \<open>beta_clause l [] = []\<close> |
  \<open>beta_clause l ((Lit pol prop) # ms) = (
    if l = (pol,prop)
    then ms
    else (Lit pol prop) # (beta_clause l ms))\<close> |
  \<open>beta_clause l ((Mat []) # ms) = \<close>*)

inductive CC (\<open>\<turnstile> _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> [] _ _\<close> |
Reduction: \<open>
  (\<turnstile> C M ((lid,pol,prp) # P)) \<Longrightarrow>
  pol \<longleftrightarrow> \<not>pol' \<Longrightarrow>
  (\<turnstile> ((_,Lit pol' prp) # C) M ((lid,pol,prp) # P))\<close> |
Permutation: \<open>
  (\<turnstile> C M P) \<Longrightarrow>
  permutation C C' \<Longrightarrow> permutation P P' \<Longrightarrow>
  (\<turnstile> C' M P')\<close> |
Extention: \<open>
  (\<turnstile> C' M ((lid,pol,prp) # P)) \<Longrightarrow>
  contains_cls (cid,C') (0,Mat M) \<Longrightarrow>
  extension_clause M P (cid,C')  \<Longrightarrow>
  (\<turnstile> C M P) \<Longrightarrow>
  (\<turnstile> ((lid,Lit pol prp) # C) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> (C' @ C) M P) \<Longrightarrow>
  member (_,C') cs \<Longrightarrow>
  (\<turnstile> ((mid,Mat cs) # C) M P)\<close>

fun CC_mat where 
  \<open>CC_mat (Lit _ _) = False\<close> |
  \<open>CC_mat (Mat []) = False\<close> |
  \<open>CC_mat (Mat ((cid,c) # m)) = (\<turnstile> c ((cid,c) # m) [])\<close>
(*-------------------------*)

(*---Generic Prop Forms----*)
datatype 'a gen_forms
  = Atm 'a
  | Neg \<open>'a gen_forms\<close>
  | Con \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>
  | Dis \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>
  | Imp \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>

fun form_to_clauses where
  \<open>form_to_clauses mx pol (Atm n) = (mx + 1,(mx,Lit pol n))\<close> |
  \<open>form_to_clauses mx pol (Neg p) = form_to_clauses mx (\<not>pol) p\<close> |
  \<open>form_to_clauses mx True (Con p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 3) True p1 in
    let (nnmx,mat2) = form_to_clauses nmx True p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1]),(mx + 2,[mat2])])))\<close> |
  \<open>form_to_clauses mx False (Dis p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 3) False p1 in
    let (nnmx,mat2) = form_to_clauses nmx False p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1]),(mx + 2,[mat2])])))\<close> |
  \<open>form_to_clauses mx False (Imp p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 3) True p1 in
    let (nnmx,mat2) = form_to_clauses nmx False p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1]),(mx + 2,[mat2])])))\<close> |
  \<open>form_to_clauses mx False (Con p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 2) False p1 in
    let (nnmx,mat2) = form_to_clauses nmx False p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1, mat2])])))\<close> |
  \<open>form_to_clauses mx True (Dis p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 2) True p1 in
    let (nnmx,mat2) = form_to_clauses nmx True p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1, mat2])])))\<close> |
  \<open>form_to_clauses mx True (Imp p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 2) False p1 in
    let (nnmx,mat2) = form_to_clauses nmx True p2 in
    (nnmx,(mx,Mat [(mx + 1,[mat1, mat2])])))\<close>

fun collaps_mat and collaps_clause where
  \<open>collaps_mat (mid,Lit pol prp) = (mid,Lit pol prp)\<close> |
  \<open>collaps_mat (mid,Mat [(_,[(mid2,Mat cs)])]) = collaps_mat (mid,Mat cs)\<close> |
  \<open>collaps_mat (mid,Mat cs) = (mid,Mat (map collaps_clause cs))\<close> | 
  \<open>collaps_clause (cid,[(mid,Mat [c])]) = collaps_clause c\<close> |
  \<open>collaps_clause (cid,ms) = (cid, (map collaps_mat ms))\<close>

(*prove idunique here*)

value \<open>form_to_clauses 0 False (Imp (Con (Imp (Atm 0) (Atm 1)) (Atm 0)) (Atm 1))\<close>
value \<open>collaps_mat 
(0,
  Mat [(1, [(3, Mat [(4, [(6, Mat [(7, [(8, Lit False 0), (9, Lit True 1)])])]),
                     (5, [(10, Lit True 0)])])]),
       (2, [(11, Lit False 1)])])\<close>

lemma \<open>CC_mat (
  Mat [
    (0, [(5,Mat [
      (1, [(6,Mat [(2, [(7,Lit False 0), (8,Lit True 1)])])]), 
      (3, [(9,Lit True 0)])])]), 
    (4, [(10,Lit False 1)])])\<close> (is \<open>CC_mat (Mat ?M)\<close>)
proof -
  have ?thesis if \<open>(\<turnstile> 
    [(5,Mat [
      (1, [(6,Mat [(2, [(7,Lit False 0), (8,Lit True 1)])])]), 
      (3, [(9,Lit True 0)])])] ?M [])\<close> 
    using that by simp
  then have ?thesis if \<open>(\<turnstile> 
    [(9,Lit True 0)] ?M [])\<close> 
    using that Decomposition by simp
  moreover have \<open>alpha_related ?M (4,[(10,Lit False 1)]) (9,Lit True 0)\<close>sorry
  ultimately have ?thesis if \<open>(\<turnstile> 
    [(10,Lit False 1)] ?M [(9,True, 0)])\<close> 
    using that Extention Axiom sorry
  then have ?thesis if \<open>(\<turnstile> 
    [Lit False 0, Lit True 1] ?M [(False,1),(True, 0)])\<close> 
    using that Extention Axiom by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit False 0, Lit True 1] ?M [(True, 0),(False,1)])\<close> 
    using that Permutation by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit True 1] ?M [(True, 0),(False,1)])\<close> 
    using that Reduction by fast
  then have ?thesis if \<open>(\<turnstile> 
    [Lit True 1] ?M [(False,1),(True, 0)])\<close> 
    using that Permutation by simp
  then show ?thesis using Reduction Axiom by simp
qed
(*-------------------------*)

(*---Paths-----------------*)
fun is_path where
  \<open>is_path p (Lit pol prop) = member (pol, prop) p\<close> |
  \<open>is_path p (Mat cs) = (\<forall> (_,ms) \<in> set cs. \<exists> m \<in> set ms. is_path p m)\<close>

definition \<open>
  cc_valid c m p \<equiv> 
    \<forall> p'. is_path p' m \<longrightarrow> (\<exists> m' \<in> set c. is_path p m') \<longrightarrow> set p \<subseteq> set p' \<longrightarrow> 
      (\<exists> prop. member (True,prop) p \<and> member (False,prop) p)\<close>

theorem cc_soundness: \<open>(\<turnstile> c m p) \<Longrightarrow> cc_valid c m p\<close>
proof (induct rule: CC.induct)
  case (Axiom uu uv)
  then show ?case 
    using cc_valid_def by simp
next
  case (Reduction C M pol prp P pol')
  then show ?case sorry
next
  case (Permutation C M P C' P')
  then show ?case sorry
next
  case (Extention C' M pol prp P C)
  then show ?case sorry
next
  case (Decomposition C' C M P uw cs)
  then show ?case sorry
qed


definition \<open>
  mat_valid m \<equiv> \<forall> p. is_path p m \<longrightarrow> (\<exists> prop. member (True,prop) p \<and> member (False,prop) p)\<close>

theorem mat_soundness: \<open>cc_valid c (Mat ((cid,c) # m)) [] \<Longrightarrow> mat_valid (Mat ((cid,c) # m))\<close> sorry
(*-------------------------*)

(*---Semantics-------------*)
primrec form_semantics where
  \<open>form_semantics i (Atm a) = i a\<close> |
  \<open>form_semantics i (Neg p) = (\<not>form_semantics i p)\<close> |
  \<open>form_semantics i (Con p1 p2) = (form_semantics i p1 \<and> form_semantics i p2)\<close> |
  \<open>form_semantics i (Dis p1 p2) = (form_semantics i p1 \<or> form_semantics i p2)\<close> |
  \<open>form_semantics i (Imp p1 p2) = (form_semantics i p1 \<longrightarrow> form_semantics i p2)\<close>

fun mat_semantics where 
  \<open>mat_semantics i (Lit pol prp) = (i prp \<longleftrightarrow> \<not>pol)\<close> |
  \<open>mat_semantics i (Mat cs) = (\<exists> (c,ms) \<in> set cs. \<forall> m \<in> set ms. mat_semantics i m)\<close>

lemma path_to_semantics_soundness: \<open>
  mat_valid m \<Longrightarrow> \<forall> i. mat_semantics i m\<close> sorry

lemma mat_to_form: \<open>
  form_to_clauses mx pol p = (n,m) \<Longrightarrow> 
  mat_semantics i m \<Longrightarrow> 
  (\<not>pol \<longleftrightarrow> form_semantics i p)\<close> 
proof (induct p arbitrary: mx pol n m)
  case (Atm a)
  then show ?case by auto
next
  case (Neg p)
  then show ?case 
    by auto
next
  case (Con p1 p2)
  then show ?case sorry
next
  case (Dis p1 p2)
  then show ?case sorry
next
  case (Imp p1 p2)
  then show ?case sorry
qed

theorem form_soundness: \<open>
  form_to_clauses 0 False p = (n,Mat ((cid,c) # cs)) \<Longrightarrow>
  (\<turnstile> c (Mat ((cid,c) # cs)) []) \<Longrightarrow>
  \<forall> i. form_semantics i p\<close> (is \<open>?translation \<Longrightarrow> ?proof \<Longrightarrow> ?valid\<close>)
proof-
  let ?m = \<open>Mat ((cid,c) # cs)\<close>
  assume t:?translation
  assume ?proof
  then have \<open>mat_valid ?m\<close>
    by (simp add: cc_soundness mat_soundness)
  then have \<open>\<forall> i. mat_semantics i ?m\<close>
    using path_to_semantics_soundness by blast
  then show ?valid 
    using mat_to_form t by blast
qed

end