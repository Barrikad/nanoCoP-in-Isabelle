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
(*-------------------------*)


(*--------NaNoCop----------*)
datatype mat 
  = Lit bool nat
  | Mat \<open>(nat \<times> mat list) list\<close>


fun exi_clause where
  \<open>exi_clause P (Lit _ _) = False\<close> |
  \<open>exi_clause P (Mat []) = False\<close> |
  \<open>exi_clause P (Mat ((n,ms) # cs)) = 
  (P (n,ms) \<or> (\<exists> m \<in> set ms. exi_clause P m) \<or> exi_clause P (Mat cs))\<close>

definition \<open>exi_mat P m \<equiv> P m \<or> exi_clause (\<lambda> (_,ms). \<exists> m' \<in> set ms. P m') m\<close>

fun all_clause where
  \<open>all_clause P (Lit _ _) = True\<close> |
  \<open>all_clause P (Mat []) = True\<close> |
  \<open>all_clause P (Mat ((n,ms) # cs)) = 
  (P (n,ms) \<and> (\<forall> m \<in> set ms. all_clause P m) \<and> all_clause P (Mat cs))\<close>

definition \<open>all_mat P m \<equiv> P m \<and> all_clause (\<lambda> (_,ms). \<forall> m' \<in> set ms. P m') m\<close>

definition \<open>id_exists idty m \<equiv> exi_clause (\<lambda> (n,_). n = idty) m\<close>

fun ids_unique where
  \<open>ids_unique (Lit b n) = True\<close> |
  \<open>ids_unique (Mat []) = True\<close> |
  \<open>ids_unique (Mat ((n,ms) # cs)) = (
    (\<forall> m \<in> set ms. ids_unique m \<and> \<not>id_exists n m) \<and> 
    \<not>id_exists n (Mat cs) \<and> 
    ids_unique (Mat cs))\<close>

primrec siblings where
  \<open>siblings c1 c2 (Lit _ _) = False\<close> |
  \<open>siblings c1 c2 (Mat cs) = (member c1 cs \<and> member c2 cs)\<close>

abbreviation \<open>
  alpha_top_level cid l m \<equiv> (\<exists> c cid' c'. 
    cid \<noteq> cid' \<and> 
    siblings (cid,c) (cid',c') m \<and> 
    (\<exists> m' \<in> set c'. exi_mat (\<lambda> l'. l = l') m'))\<close>

definition \<open>
  alpha_related m cid l \<equiv> 
    exi_mat (alpha_top_level cid l) m\<close>

primrec union_many where
  \<open>union_many [] = {}\<close> |
  \<open>union_many (xs # ys) = xs \<union> (union_many ys)\<close>

abbreviation \<open>permutation xs ys \<equiv> length xs = length ys \<and> set xs = set ys\<close>

(*fun beta_clause where
  \<open>beta_clause l [] = []\<close> |
  \<open>beta_clause l ((Lit pol prop) # ms) = (
    if l = (pol,prop)
    then ms
    else (Lit pol prop) # (beta_clause l ms))\<close> |
  \<open>beta_clause l ((Mat []) # ms) = \<close>*)

inductive CC' (\<open>\<turnstile> _ _ _\<close> 0) where 
Axiom: \<open>\<turnstile> [] _ _\<close> |
Reduction: \<open>
  (\<turnstile> C M ((pol,prop) # P)) \<Longrightarrow>
  pol \<longleftrightarrow> \<not>pol' \<Longrightarrow>
  (\<turnstile> ((Lit pol' prop) # C) M ((pol,prop) # P))\<close> |
Permutation: \<open>
  (\<turnstile> C M P) \<Longrightarrow>
  permutation C C' \<Longrightarrow> permutation P P' \<Longrightarrow>
  (\<turnstile> C' M P')\<close> |
Extention: \<open>
  (\<turnstile> C' M ((pol,prop) # P)) \<Longrightarrow>
  exi_clause (\<lambda> (cid,C). C = C') M \<Longrightarrow>
  (\<turnstile> C M P) \<Longrightarrow>
  (\<turnstile> ((Lit pol prop) # C) M P)\<close> |
Decomposition: \<open>
  (\<turnstile> (C' @ C) M P) \<Longrightarrow>
  member (_,C') cs \<Longrightarrow>
  (\<turnstile> ((Mat cs) # C) M P)\<close>

fun CC where 
  \<open>CC (Lit _ _) = False\<close> |
  \<open>CC (Mat []) = False\<close> |
  \<open>CC (Mat ((cid,c) # m)) = (\<turnstile> c (Mat ((cid,c) # m)) [])\<close>
(*-------------------------*)

(*---Generic Prop Forms----*)
datatype 'a gen_forms
  = Atm 'a
  | Neg \<open>'a gen_forms\<close>
  | Con \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>
  | Dis \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>
  | Imp \<open>'a gen_forms\<close> \<open>'a gen_forms\<close>

fun form_to_clauses where
  \<open>form_to_clauses mx pol (Atm n) = (mx,Lit pol n)\<close> |
  \<open>form_to_clauses mx pol (Neg p) = form_to_clauses mx (\<not>pol) p\<close> |
  \<open>form_to_clauses mx True (Con p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) True p1 in
    let (nnmx,mat2) = form_to_clauses (nmx + 1) True p2 in
    (nnmx,Mat [(mx,[mat1]),(nmx,[mat2])]))\<close> |
  \<open>form_to_clauses mx False (Dis p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) False p1 in
    let (nnmx,mat2) = form_to_clauses (nmx + 1) False p2 in
    (nnmx,Mat [(mx,[mat1]),(nmx,[mat2])]))\<close> |
  \<open>form_to_clauses mx False (Imp p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) True p1 in
    let (nnmx,mat2) = form_to_clauses (nmx + 1) False p2 in
    (nnmx,Mat [(mx,[mat1]),(nmx,[mat2])]))\<close> |
  \<open>form_to_clauses mx False (Con p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) False p1 in
    let (nnmx,mat2) = form_to_clauses nmx False p2 in
    (nnmx,Mat [(mx,[mat1, mat2])]))\<close> |
  \<open>form_to_clauses mx True (Dis p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) True p1 in
    let (nnmx,mat2) = form_to_clauses nmx True p2 in
    (nnmx,Mat [(mx,[mat1, mat2])]))\<close> |
  \<open>form_to_clauses mx True (Imp p1 p2) = (
    let (nmx,mat1) = form_to_clauses (mx + 1) False p1 in
    let (nnmx,mat2) = form_to_clauses nmx True p2 in
    (nnmx,Mat [(mx,[mat1, mat2])]))\<close>

(*prove idunique here*)

value \<open>form_to_clauses 0 False (Imp (Con (Imp (Atm 0) (Atm 1)) (Atm 0)) (Atm 1))\<close>

lemma \<open>CC (
  Mat [
    (0, [Mat [
      (1, [Mat [(2, [Lit False 0, Lit True 1])]]), 
      (3, [Lit True 0])]]), 
    (4, [Lit False 1])])\<close> (is \<open>CC ?M\<close>) 
proof -
  have ?thesis if \<open>(\<turnstile> 
    [Mat [(1, [Mat [(2, [Lit False 0, Lit True 1])]]), (3, [Lit True 0])]] ?M [])\<close> 
    using that by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit True 0] ?M [])\<close> 
    using that Decomposition by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit False 1] ?M [(True, 0)])\<close> 
    using that Extention Axiom by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit False 0, Lit True 1] ?M [(False,1),(True, 0)])\<close> 
    using that Extention Axiom by simp
  then have ?thesis if \<open>(\<turnstile> 
    [Lit False 0, Lit True 1] ?M [(True, 0),(False,1)])\<close> 
    using that Permutation by force
  then have ?thesis if \<open>(\<turnstile> 
    [Lit True 1] ?M [(True, 0),(False,1)])\<close> 
    using that Reduction by fast
  then have ?thesis if \<open>(\<turnstile> 
    [Lit True 1] ?M [(False,1),(True, 0)])\<close> 
    using that Permutation by force
  then show ?thesis using Reduction Axiom by simp
qed
(*-------------------------*)

(*---Paths-----------------*)
fun is_path_mat where
  \<open>is_path_mat p (Lit pol prop) = member (Lit pol prop) p\<close> |
  \<open>is_path_mat p (Mat cs) = (\<forall> (_,ms) \<in> set cs. \<exists> m \<in> set ms. is_path_mat p m)\<close>

end