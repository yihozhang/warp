use crate::{Math, Meta, Schema};

use egg::{rewrite as rw, Applier, Pattern, Rewrite};

use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};

#[rustfmt::skip]
pub fn untrans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        rw!("ra-minus"; "(l+ ?a (l* (llit -1) ?b))" => "(l- ?a ?b)"),
        rw!("ra-elim-bind0"; "(b- ?i ?j (b+ ?i ?j ?x))" => "?x"),
        // rw!("ra-elim-bind1"; "(b+ ?i ?j (b- ?i _ ?x))" => "?x"),
        // rw!("ra-elim-bind2"; "(b+ ?i ?j (b- _ ?j ?x))" => "?x"),
        // rw!("ra-elim-bind3"; "(b+ ?i ?j (b- _ _ ?x))" => "?x"),
        rw!("ra-unbind-lit"; "(b- ?i ?j (lit ?n))" => "(llit ?n)"),
        rw!("ra_sall"; "(srow (scol ?x))" => "(sall ?x)"),
        rw!("ra_sall2"; "(scol (srow ?x))" => "(sall ?x)"),
        rw!("ra_mat1"; "(mat ?x (dim ?i ?n) (dim ?j ?m) (nnz ?z))" => "(b+ ?i ?j (lmat ?x ?n ?m ?z))"),
        //rw!("ra_mat2"; "(mat ?x (dim ?i ?n) (dim ?j ?m) (nnz ?z))" => "(b+ ?j ?i (lmat ?x ?m ?n ?z))"),
        rw!("ra_transpose"; "(b- ?j ?i (b+ ?i ?j ?x))" => "(trans ?x)"),
        rw!("ra_lit"; "(lit ?n)" => "(b+ _ _ (llit ?n))"),
        rw!("sum_d1"; "(sum (dim _ 1) ?x)" => "?x"),
        rw!("ra-bind"; "?e" => {RABind}),
        rw!("ra-add"; "(+ ?a ?b)" => {RAAdd}),
        rw!("ra-mul"; "(* ?a ?b)" => {RAMul}),
        rw!("ra-sum"; "(sum ?i ?x)" => {RASum}),
        rw!("ra-mmul2"; "(rm* ?a ?b)" => {RARMMul}),
    ]
}

#[rustfmt::skip]
pub fn trans_rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        // TODO b(^) is probability parsed as b (^)
        rw!("la-sq"; "(udf b(^) ?x (llit 2))" => "(l* ?x ?x)"),
        rw!("la-minus"; "(l- ?a ?b)" => "(l+ ?a (l* (llit -1) ?b))"),
        rw!("la-mat-bind"; "(b+ ?k ?l (lmat ?x ?i ?j ?z))" => "(mat ?x (dim ?k ?i) (dim ?l ?j) (nnz ?z))"),
        rw!("la-lit-bind"; "(b+ ?i ?j (llit ?n))" => "(lit ?n)"),
        rw!("la-lit-ubnd"; "(llit ?n)" => "(b- _ _ (lit ?n))"),
        rw!("subst-+"; "(subst ?e ?v (+ ?a ?b))" => "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-*"; "(subst ?e ?v (* ?a ?b))" => "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-matrix"; "(subst ?e ?v (mat ?a ?i ?j ?z))" => "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw!("subst-lit"; "(subst ?e ?v (lit ?n))" => "(lit ?n)"),
        rw!("subst-var"; "(subst ?e ?v (var ?n))" => "(var ?n)"),
        rw!("subst-udf1"; "(subst ?e ?v (udf ?op ?x))" => "(udf ?op (subst ?e ?v ?x))"),
        rw!("subst-udf2"; "(subst ?e ?v (udf ?op ?x ?y))" => "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y))"),
        rw!("subst-udf3"; "(subst ?e ?v (udf ?op ?x ?y ?z))" => "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z))"),
        rw!("subst-udf4"; "(subst ?e ?v (udf ?op ?x ?y ?z ?u))" => "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u))"),
        rw!("subst-udf5"; "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w))" =>
           "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w))"),
        rw!("subst-udf6"; "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a))" =>
           "(udf ?op (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) (subst ?e ?v ?a))"),
        rw!("subst-rix"; "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a ?b))" =>
           "(udf rix (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) ?a ?b)"),
        rw!("subst-udf8"; "(subst ?e ?v (udf ?op ?x ?y ?z ?u ?w ?a ?b ?c))" =>
           "(udf lix (subst ?e ?v ?x) (subst ?e ?v ?y) (subst ?e ?v ?z) (subst ?e ?v ?u) (subst ?e ?v ?w) (subst ?e ?v ?a) ?b ?c)"),
        // NOTE this makes a loop and will triger stack overflow
        rw!("subst-wild"; "(subst (dim _ ?i) (dim _ ?j) ?e)" => "?e"),
        rw!("la_lmat"; "(lmat ?x ?i ?j ?z)" => {LAMat}),
        rw!("la_mul"; "(l* ?x ?y)" => {LAMul}),
        rw!("la_add"; "(l+ ?x ?y)" => {LAAdd}),
        rw!("la_mmul"; "(m* ?x ?y)" => {LAMMul}),
        rw!("la-srow"; "(srow ?a)" => {LASrow}),
        rw!("la-scol"; "(scol ?a)" => {LAScol}),
        rw!("la-sall"; "(sall ?a)" => {LASall}),
        rw!("la-trans"; "(trans ?a)" => {LATrans}),
        rw!("la-bind"; "(b+ ?k ?l (b- ?i ?j ?x))" => {LABind}),
        rw!("subst-bind"; "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))" => {SubstBind}),
        rw!("agg-subst"; "(subst ?e ?v1 (sum ?v2 ?body))" => {SubstAgg}),
        rw!("dim_subst"; "(subst ?e (dim ?v ?m) (dim ?i ?n))" => {DimSubst}),
    ]
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite<Math, Meta>> {
    vec![
        // NOTE subst e v x is x[v => e]
        // NOTE udf b(m1mul) breaks b/c parsing
        // rw!("bindudf"; "(b+ ?i ?j (udf ?o ?x ?y))" => "(b+ ?i ?j (udf ?o (b- ?i ?j (b+ ?i ?j ?x)) (b- ?i ?j (b+ ?i ?j ?y))))"),
        // rw!("la-bind"; "(b+ ?k ?l (b- ?i ?j ?x))" => {LABind}),
        rw!("trivial-id"; "(sum ?w (* (ind ?x (mat ?i ?w ?w ?n)) (mat ?i ?w ?w ?n)))" => "?x"),
        rw!("+-commutative"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("*-commutative"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("associate-+r+"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("associate-+l+"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("associate-*r*"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("associate-*l*"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rw!("subst-+"; "(subst ?e ?v (+ ?a ?b))" => "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("subst-*"; "(subst ?e ?v (* ?a ?b))" => "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
        rw!("add-2-mul"; "(+ ?x ?x)" => "(* (lit 2) ?x)"),
        rw!("subst-matrix"; "(subst ?e ?v (mat ?a ?i ?j ?z))" => "(mat ?a (subst ?e ?v ?i) (subst ?e ?v ?j) ?z)"),
        rw!("subst-lit"; "(subst ?e ?v (lit ?n))" => "(lit ?n)"),
        rw!("subst-var"; "(subst ?e ?v (var ?n))" => "(var ?n)"),
        rw!("subst-bind"; "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))" => {SubstBind}),
        rw!("distribute-lft-in"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("distribute-rgt-in"; "(* ?a (+ ?b ?c))" => "(+ (* ?b ?a) (* ?c ?a))"),
        rw!("distribute-lft-out"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // rw!("distribute-lft-out--"; "(- (* ?a ?b) (* ?a ?c))" => "(* ?a (- ?b ?c))"),
        rw!("distribute-rgt-out"; "(+ (* ?b ?a) (* ?c ?a))" => "(* ?a (+ ?b ?c))"),
        // rw!("distribute-rgt-out--"; "(- (* ?b ?a) (* ?c ?a))" => "(* ?a (- ?b ?c))"),
        rw!("distribute-lft1-in"; "(+ (* ?b ?a) ?a)" => "(* (+ ?b (lit 1)) ?a)"),
        rw!("distribute-rgt1-in"; "(+ ?a (* ?c ?a))" => "(* (+ ?c (lit 1)) ?a)"),
        rw!("pullup-add"; "(sum ?i (+ ?a ?b))" => "(+ (sum ?i ?a) (sum ?i ?b))"),
        rw!("pushdown-add"; "(+ (sum ?i ?a) (sum ?i ?b))" => "(sum ?i (+ ?a ?b))"),
        rw!("swap-agg"; "(sum ?i (sum ?j ?a))" => "(sum ?j (sum ?i ?a))"),
        rw!("sum_i_a"; "(sum ?i ?a)" => {SumIA}),
        rw!("pullup_mul"; "(sum ?i (* ?a ?b))" => {PullMul}),
        rw!("pushdown_mul"; "(* ?a (sum ?i ?b))" => {PushMul}),
        rw!("agg-subst"; "(subst ?e ?v1 (sum ?v2 ?body))" => {SubstAgg}),
        rw!("dim_subst"; "(subst ?e (dim ?v ?m) (dim ?i ?n))" => {DimSubst}),
        rw!("mmul"; "(sum ?j (* ?a ?b))" => {AggMMul}),
        // rw!("m1mul"; "(+ (lit 1) (* (lit -1) (* ?x ?y)))" => {MOneMul}),
        // rw!("axpy"; "(+ ?x (* ?p ?y))" => {Axpy}),
        // rw!("sprop"; "(* ?x (+ (lit 1) (* (lit -1) ?x)))" => {Sprop}),
        // rw!("udf_rename"; "(b+ ?i ?j (udf ?o (b- ?k ?l ?x) (b- ?m ?n ?y)))" => {UdfRn}),
        // TODO need bind ubnd below
        // rw!("selp"; "(* ?x (b+ ?i ?j (udf b(>) (b- ?k ?l ?x) (b- _ _ (lit 0)))))" => "(b+ ?i ?j (udf selp (b- ?k ?l ?x)))"),
        // selp rule omitted: pattern uses b(>) which can't be expressed as a plain s-expr string
        // and requires programmatic PatternAst construction (TODO: port to new egg PatternAst API)
        rw!("sum_"; "(sum (dim _ 1) ?x)" => "(* (lit 1) ?x)"),
        //drw("foundit",
        //    "(+ (sum ?i (sum ?j (+ (* (mat ?x ?i ?j ?za) (mat ?x ?i ?j ?zb)) (+ \
        //     (* (mat ?x ?i ?j ?zc) (sum ?k (* (mat ?u ?i ?k ?zd) (mat ?v ?k ?j ?ze)))) \
        //     (* (mat ?x ?i ?j ?zf) (sum ?k (* (mat ?u ?i ?k ?zg) (mat ?v ?k ?j ?zh)))))))) \
        //     (sum ?c (sum ?a (* \
        //     (sum ?b (* (mat ?u ?a ?b ?zi) (mat ?u ?b ?c ?zj)))\
        //     (sum ?d (* (mat ?v ?a ?d ?zk) (mat ?v ?d ?c ?zl)))))))",
        //    Foundit
        //)
    ]
}

#[allow(unused)]
#[derive(Debug)]
struct Axpy;
impl Applier<Math, Meta> for Axpy {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm();
        let p = subst["?p".parse::<egg::Var>().unwrap()];
        let p_schema = egraph[p].data.schema.as_ref().unwrap().get_schm();
        let y = subst["?y".parse::<egg::Var>().unwrap()];
        let y_schema = egraph[y].data.schema.as_ref().unwrap().get_schm();

        let mut res = vec![];
        if p_schema.is_empty() && x_schema.len() == 2 && x_schema == y_schema {
            let mut x_schema = x_schema.keys();
            let wc = "_".to_owned();
            let i = x_schema.next().unwrap_or(&wc).clone();
            let j = x_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = format!(
                "(b+ {i} {j} (udf axpy (b- {i} {j} ?x) (b- _ _ ?p) (b- {i} {j} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ij);
            let mut bind_ji = format!(
                "(b+ {j} {i} (udf axpy (b- {j} {i} ?x) (b- _ _ ?p) (b- {j} {i} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ji);
        }
        res
    }
}

#[allow(unused)]
#[derive(Debug)]
struct UdfRn;
impl Applier<Math, Meta> for UdfRn {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // (b+ ?i ?j (udf ?o (b- ?k ?l ?x) (b- ?m ?n ?y)))
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let i_str = egraph[i].data.schema.as_ref().unwrap().get_name();
        let j = subst["?j".parse::<egg::Var>().unwrap()];
        let j_str = egraph[j].data.schema.as_ref().unwrap().get_name();
        let k = subst["?k".parse::<egg::Var>().unwrap()];
        let k_str = egraph[k].data.schema.as_ref().unwrap().get_name();
        let l = subst["?l".parse::<egg::Var>().unwrap()];
        let l_str = egraph[l].data.schema.as_ref().unwrap().get_name();
        let m = subst["?m".parse::<egg::Var>().unwrap()];
        let m_str = egraph[m].data.schema.as_ref().unwrap().get_name();
        let n = subst["?n".parse::<egg::Var>().unwrap()];
        let n_str = egraph[n].data.schema.as_ref().unwrap().get_name();
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm();
        let y = subst["?y".parse::<egg::Var>().unwrap()];
        let y_schema = egraph[y].data.schema.as_ref().unwrap().get_schm();

        let subxi = if k_str == "_" || k_str == i_str {
            "?x".to_owned()
        } else {
            format!("(subst (dim ?i {n}) (dim ?k {n}) ?x)", n = x_schema[k_str])
        };
        let subxj = if l_str == "_" || l_str == j_str {
            subxi
        } else {
            format!(
                "(subst (dim ?j {n}) (dim ?l {n}) {sxi})",
                n = x_schema[l_str],
                sxi = subxi
            )
        };
        let subyi = if m_str == "_" || m_str == i_str {
            "?y".to_owned()
        } else {
            format!("(subst (dim ?i {n}) (dim ?m {n}) ?y)", n = y_schema[m_str])
        };
        let subyj = if n_str == "_" || n_str == j_str {
            subyi
        } else {
            format!(
                "(subst (dim ?j {n}) (dim ?n {n}) {syi})",
                n = y_schema[n_str],
                syi = subyi
            )
        };
        let (xi, _xa) = if k_str == "_" {
            ("_", 1)
        } else {
            ("?i", x_schema[k_str])
        };
        let (xj, _xb) = if l_str == "_" {
            ("_", 1)
        } else {
            ("?j", x_schema[l_str])
        };
        let (yi, _ya) = if m_str == "_" {
            ("_", 1)
        } else {
            ("?i", y_schema[m_str])
        };
        let (yj, _yb) = if n_str == "_" {
            ("_", 1)
        } else {
            ("?j", y_schema[n_str])
        };

        format!(
            "(b+ ?i ?j (udf ?o (b- {xi} {xj} {sxj}) (b- {yi} {yj} {syj})))",
            xi = xi,
            xj = xj,
            yi = yi,
            yj = yj,
            sxj = subxj,
            syj = subyj,
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)

        // "(b+ ?i ?j (udf ?o (b- ?k ?l ?x) (b- ?m ?n ?y)))"
        // Math::parse_pattern(
        //     format!(
        //         "(b+ ?i ?j (udf ?o (b- {xi} {xj} (subst (dim {xi} {xa}) (dim ?k {xa}) (subst (dim {xj} {xb}) (dim ?l {xb}) ?x))) (b- {yi} {yj} (subst (dim {yi} {ya}) (dim ?m {ya}) (subst (dim {yj} {yb}) (dim ?n {yb}) ?y)))))",
        //         xi = xi, xj = xj, xa = xa, xb = xb,
        //         yi = yi, yj = yj, ya = ya, yb = yb
        //     )
        // ).unwrap().apply_one(egraph, eclass, subst, searcher_ast, rule_name)

        // (b+ ?i ?j (udf ?o (b- ?xi ?xj (subst (?i {b}) (?k {b}) (subst (?j {a}) (?l {a}) ?x)) (subst ?i ?m (subst ?j ?n ?y)))))

        // let sjx = if l_str == "_" {
        //     AddResult {
        //         was_there: true,
        //         id: x
        //     }
        // } else {
        //     let n = x_schema[l_str];
        //     let mut added = Math::parse_pattern(
        //         format!(
        //             "(subst (dim ?j {n}) (dim ?l {n}) ?x)",
        //             n = n
        //         )
        //     ).unwrap().apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        //     debug_assert_eq!(added.len(), 1);
        //     added.pop().unwrap()
        // };
    }
}

#[allow(unused)]
#[derive(Debug)]
struct Sprop;
impl Applier<Math, Meta> for Sprop {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // (b+ i j (sprop (b- i j ?x)))
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let mut x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm().keys();
        let mut res = vec![];
        if x_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = x_schema.next().unwrap_or(&wc).clone();
            let j = x_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = format!("(b+ {i} {j} (udf sprop (b- {i} {j} ?x)))", i = &i, j = &j)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ij);

            let mut bind_ji = format!("(b+ {j} {i} (udf sprop (b- {j} {i} ?x)))", i = &i, j = &j)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ji);
        }
        res
    }
}

#[allow(unused)]
#[derive(Debug)]
struct MOneMul;
impl Applier<Math, Meta> for MOneMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // rw!("m1mul"; "(+ (lit 1) (* (lit -1) (* ?x ?y)))" => {MOneMul}),
        // (b+ i j (udf m1mul (b- i j x) (b- i j y)))
        // get x schema, unbind
        // get y schema, unbind
        // get result schema, bind

        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let y = subst["?y".parse::<egg::Var>().unwrap()];
        let mul = egraph.add(Math::Mul([x, y]));
        let mut mul_schema = egraph[mul].data.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if mul_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = mul_schema.next().unwrap_or(&wc).clone();
            let j = mul_schema.next().unwrap_or(&wc).clone();

            let mut bind_ij = format!(
                "(b+ {i} {j} (udf m1mul (b- {i} {j} ?x) (b- {i} {j} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ij);

            let mut bind_ji = format!(
                "(b+ {j} {i} (udf m1mul (b- {j} {i} ?x) (b- {j} {i} ?y)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ji);
        }
        res
    }
}

#[derive(Debug)]
struct AggMMul;

impl Applier<Math, Meta> for AggMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let j = subst["?j".parse::<egg::Var>().unwrap()];
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let b = subst["?b".parse::<egg::Var>().unwrap()];

        let a_schema = &egraph[a].data.schema.as_ref().unwrap().get_schm().clone();
        let a_s: HashSet<_> = a_schema.keys().cloned().collect();
        let b_schema = &egraph[b].data.schema.as_ref().unwrap().get_schm().clone();
        let b_s: HashSet<_> = b_schema.keys().cloned().collect();
        let i: Vec<_> = a_s.intersection(&b_s).collect();
        let j_schema = &egraph[j].data.schema.as_ref().unwrap().get_dims().0.clone();

        if a_schema.len() <= 2 && b_schema.len() <= 2 && i.len() == 1 && i[0] == j_schema {
            format!("(rm* ?a ?b)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            vec![]
        }
    }
}

#[allow(unused)]
#[derive(Debug)]
struct Foundit;

impl Applier<Math, Meta> for Foundit {
    fn apply_one(
        &self,
        _egraph: &mut egg::EGraph<Math, Meta>,
        _eclass: egg::Id,
        _subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<Math>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        panic!("FOUNDITTT")
    }
}

#[derive(Debug)]
struct SubstAgg;

impl Applier<Math, Meta> for SubstAgg {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<Math>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let v1 = subst["?v1".parse::<egg::Var>().unwrap()];
        let v2 = subst["?v2".parse::<egg::Var>().unwrap()];
        let e = subst["?e".parse::<egg::Var>().unwrap()];
        let body = subst["?body".parse::<egg::Var>().unwrap()];

        let res = if v1 == v2 {
            egraph.add(Math::Agg([v2, body]))
        } else {
            let sub_body = egraph.add(Math::Sub([e, v1, body]));
            egraph.add(Math::Agg([v2, sub_body]))
        };
        egraph.union(eclass, res);

        vec![res]
    }
}

// rw!("subst-bind"; "(subst (dim ?j ?m) (dim ?i ?n) (b+ ?k ?l ?e))" => {SubstBind}),
#[derive(Debug)]
struct SubstBind;
impl Applier<Math, Meta> for SubstBind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let k = subst["?k".parse::<egg::Var>().unwrap()];
        let l = subst["?l".parse::<egg::Var>().unwrap()];

        if i == k {
            format!("(b+ ?j ?l ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else if i == l {
            format!("(b+ ?k ?j ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            format!("(b+ ?k ?l ?e)")
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

#[derive(Debug)]
struct SumIA;
impl Applier<Math, Meta> for SumIA {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let i_m = &egraph[i].data;
        let (k, n) = i_m.schema.as_ref().unwrap().get_dims();

        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_m = &egraph[a].data;
        let body = a_m.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            format!("(* ?a (lit {n}))", n = *n as i32)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PullMul;

impl Applier<Math, Meta> for PullMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let i_schema = &egraph[i].data;
        let k = i_schema.schema.as_ref().unwrap().get_dims().0;

        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_schema = &egraph[a].data;
        let body = a_schema.schema.as_ref().unwrap().get_schm();

        if !body.contains_key(k) {
            "(* ?a (sum ?i ?b))"
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
struct PushMul;
impl Applier<Math, Meta> for PushMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let b = subst["?b".parse::<egg::Var>().unwrap()];

        let (i_s, i_n) = egraph[i].data.schema.as_ref().unwrap().get_dims();
        let a_schema = egraph[a].data.schema.as_ref().unwrap().get_schm();

        if !a_schema.contains_key(i_s) {
            "(sum ?i (* ?a ?b))"
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            let mut s = DefaultHasher::new();
            [i, a, b].hash(&mut s);
            let fresh_s = format!("v{s}", s = &(s.finish() % 976521).to_string());

            format!(
                "(sum (dim {fv} {fn}) (* ?a (subst (dim {fv} {fn}) ?i ?b)))",
                fv=&fresh_s, fn=*i_n as i32
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

#[derive(Debug)]
struct DimSubst;
impl Applier<Math, Meta> for DimSubst {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        _searcher_ast: Option<&egg::PatternAst<Math>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let e = subst["?e".parse::<egg::Var>().unwrap()];
        let v = subst["?v".parse::<egg::Var>().unwrap()];
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let n = subst["?n".parse::<egg::Var>().unwrap()];

        let res = if i == v {
            e
        } else {
            egraph.add(Math::Dim([i, n]))
        };
        egraph.union(eclass, res);

        vec![res]
    }
}

#[derive(Debug)]
struct LAMul;

impl Applier<Math, Meta> for LAMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let y = subst["?y".parse::<egg::Var>().unwrap()];
        let x_schema = egraph[x].data.clone().schema.unwrap();
        let (x_i, x_j) = x_schema.get_mat();
        let y_schema = egraph[y].data.clone().schema.unwrap();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = format!("vmul_i{}", &fresh_s);
        let fresh_j = format!("vmul_j{}", &fresh_s);

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yi = if *y_i == 1 { "_" } else { &fresh_i };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };
        let ubnd_i = if x_i * y_i == 1 { "_" } else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} {j} (* (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
            i = ubnd_i,
            j = ubnd_j,
            xi = bind_xi,
            xj = bind_xj,
            yi = bind_yi,
            yj = bind_yj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LAMat;
impl Applier<Math, Meta> for LAMat {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // (lmat x i j z)
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let j = subst["?j".parse::<egg::Var>().unwrap()];
        let z = subst["?i".parse::<egg::Var>().unwrap()];

        let i_schema = egraph[i].data.clone().schema.unwrap();
        let x_i = i_schema.get_size();
        let j_schema = egraph[j].data.clone().schema.unwrap();
        let x_j = j_schema.get_size();

        let mut s = DefaultHasher::new();
        [x, i, j, z].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = format!("vmat_i{}", &fresh_s);
        let fresh_j = format!("vmat_j{}", &fresh_s);
        let bind_i = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_j = if *x_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} {j} (mat ?x (dim {i} ?i) (dim {j} ?j) (nnz ?z)))",
            i = bind_i,
            j = bind_j
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LAAdd;

impl Applier<Math, Meta> for LAAdd {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let y = subst["?y".parse::<egg::Var>().unwrap()];

        let x_schema = egraph[x].data.clone().schema.unwrap();
        let y_schema = egraph[y].data.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_i, y_j) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vadd_i".to_owned() + &fresh_s;
        let fresh_j = "vadd_j".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yi = if *y_i == 1 { "_" } else { &fresh_i };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };

        let ubnd_i = if x_i * y_i == 1 { "_" } else { &fresh_i };
        let ubnd_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        // [-i,j] (* [i,j]A [i,j]B)
        format!(
            "(b- {i} {j} (+ (b+ {xi} {xj} ?x) (b+ {yi} {yj} ?y)))",
            i = &ubnd_i,
            j = &ubnd_j,
            xi = &bind_xi,
            xj = &bind_xj,
            yi = &bind_yi,
            yj = &bind_yj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LAMMul;
impl Applier<Math, Meta> for LAMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let y = subst["?y".parse::<egg::Var>().unwrap()];

        let x_schema = egraph[x].data.clone().schema.unwrap();
        let y_schema = egraph[y].data.clone().schema.unwrap();

        let (x_i, x_j) = x_schema.get_mat();
        let (y_j, y_k) = y_schema.get_mat();

        let mut s = DefaultHasher::new();
        [x, y].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vmmul_i".to_owned() + &fresh_s;
        let fresh_j = "vmmul_j".to_owned() + &fresh_s;
        let fresh_k = "vmmul_k".to_owned() + &fresh_s;

        let bind_xi = if *x_i == 1 { "_" } else { &fresh_i };
        let bind_xj = if *x_j == 1 { "_" } else { &fresh_j };
        let bind_yj = if *y_j == 1 { "_" } else { &fresh_j };
        let bind_yk = if *y_k == 1 { "_" } else { &fresh_k };

        let ubnd_i = if *x_i == 1 { "_" } else { &fresh_i };
        let ubnd_k = if *y_k == 1 { "_" } else { &fresh_k };

        let agg_j = if x_j * y_j == 1 { "_" } else { &fresh_j };

        if agg_j == "_" {
            format!(
                "(b- {i} {k} (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y)))",
                i = &ubnd_i,
                k = &ubnd_k,
                xi = &bind_xi,
                xj = &bind_xj,
                yj = &bind_yj,
                yk = &bind_yk
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            format!(
                "(b- {i} {k} (sum (dim {j} {j_n}) (* (b+ {xi} {xj} ?x) (b+ {yj} {yk} ?y))))",
                i = &ubnd_i,
                k = &ubnd_k,
                j = &agg_j,
                j_n = *x_j as i32,
                xi = &bind_xi,
                xj = &bind_xj,
                yj = &bind_yj,
                yk = &bind_yk,
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

#[derive(Debug)]
struct LATrans;

impl Applier<Math, Meta> for LATrans {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vtrans_i".to_owned() + &fresh_s;
        let fresh_j = "vtrans_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!("(b- {j} {i} (b+ {i} {j} ?a))", j = &bind_aj, i = &bind_ai)
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LASrow;

impl Applier<Math, Meta> for LASrow {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- {i} _ (sum (dim {j} {jn}) (b+ {i} {j} ?a)))",
            i = &bind_ai,
            jn = *a_j as i32,
            j = &bind_aj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LAScol;

impl Applier<Math, Meta> for LAScol {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsrow_i".to_owned() + &fresh_s;
        let fresh_j = "vsrow_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- _ {j} (sum (dim {i} {in}) (b+ {i} {j} ?a)))",
            i=&bind_ai, in=*a_i as i32, j=&bind_aj
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LASall;

impl Applier<Math, Meta> for LASall {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let a_schema = egraph[a].data.schema.as_ref().unwrap();
        let (a_i, a_j) = a_schema.get_mat();

        let mut s = DefaultHasher::new();
        [a].hash(&mut s);
        let fresh_s = (s.finish() % 976521).to_string();
        let fresh_i = "vsall_i".to_owned() + &fresh_s;
        let fresh_j = "vsall_j".to_owned() + &fresh_s;

        let bind_ai = if *a_i == 1 { "_" } else { &fresh_i };
        let bind_aj = if *a_j == 1 { "_" } else { &fresh_j };

        format!(
            "(b- _ _ (sum (dim {i} {in}) (sum (dim {j} {jn}) (b+ {i} {j} ?a))))",
            i=&bind_ai, in=*a_i as i32, j=&bind_aj, jn=*a_j as i32
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct LABind;

impl Applier<Math, Meta> for LABind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let j = subst["?j".parse::<egg::Var>().unwrap()];
        let k = subst["?k".parse::<egg::Var>().unwrap()];
        let l = subst["?l".parse::<egg::Var>().unwrap()];
        let x = subst["?x".parse::<egg::Var>().unwrap()];

        let i_schema = egraph[i].data.schema.as_ref().unwrap().get_name();
        let j_schema = egraph[j].data.schema.as_ref().unwrap().get_name();
        let k_schema = egraph[k].data.schema.as_ref().unwrap().get_name();
        let l_schema = egraph[l].data.schema.as_ref().unwrap().get_name();
        let x_schema = egraph[x].data.schema.as_ref().unwrap().get_schm();
        let (x_i, x_j) = (
            *x_schema.get(i_schema).unwrap_or(&1),
            *x_schema.get(j_schema).unwrap_or(&1),
        );

        if l_schema == "_" {
            assert_eq!(j_schema, "_", "unbinding wildcard");
        }
        if k_schema == "_" {
            assert_eq!(i_schema, "_", "unbinding wildcard");
        }

        format!(
            "(subst (dim {l} {jn}) (dim {j} {jn}) (subst (dim {k} {in}) (dim {i} {in}) ?x))",
            l=&l_schema.clone(), jn=x_j as i32, j=&j_schema.clone(),
            k=&k_schema.clone(), in=x_i as i32, i=&i_schema.clone()
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
    }
}

#[derive(Debug)]
struct RAAdd;

impl Applier<Math, Meta> for RAAdd {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let b = subst["?b".parse::<egg::Var>().unwrap()];
        let add = egraph.add(Math::Add([a, b]));
        let mut add_schema = egraph[add].data.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if add_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = add_schema.next().unwrap_or(&wc).clone();
            let j = add_schema.next().unwrap_or(&wc).clone();
            // TODO change this as mul

            let mut bind_ij = format!(
                "(b+ {i} {j} (l+ (b- {i} {j} ?a) (b- {i} {j} ?b)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ij);

            let mut bind_ji = format!(
                "(b+ {j} {i} (l+ (b- {j} {i} ?a) (b- {j} {i} ?b)))",
                i = &i,
                j = &j
            )
            .parse::<Pattern<Math>>()
            .unwrap()
            .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut bind_ji);
        }
        res
    }
}

#[derive(Debug)]
struct RAMul;

impl Applier<Math, Meta> for RAMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let b = subst["?b".parse::<egg::Var>().unwrap()];
        let mul = egraph.add(Math::Mul([a, b]));
        egraph.rebuild();
        // let mul_meta = &egraph[mul].data;
        let mul_schema: Vec<String> = egraph[mul]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .cloned()
            .collect();
        let a_schema: HashSet<_> = egraph[a]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .filter(|&k| k != "_")
            .collect();
        let b_schema: HashSet<_> = egraph[b]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .filter(|&k| k != "_")
            .collect();

        let mut res = vec![];
        if mul_schema.len() <= 2 {
            let wc = "_".to_owned();
            let i = mul_schema.get(0).unwrap_or(&wc).clone();
            let j = mul_schema.get(1).unwrap_or(&wc).clone();
            let ai = if let None = a_schema.get(&i) { &wc } else { &i };
            let aj = if let None = a_schema.get(&j) { &wc } else { &j };
            let bi = if let None = b_schema.get(&i) { &wc } else { &i };
            let bj = if let None = b_schema.get(&j) { &wc } else { &j };

            if a_schema.is_subset(&b_schema) || b_schema.is_subset(&a_schema) {
                let bij = format!(
                    "(b+ {i} {j} (l* (b- {ai} {aj} ?a) (b- {bi} {bj} ?b)))",
                    i = &i,
                    j = &j,
                    ai = &ai,
                    aj = &aj,
                    bi = &bi,
                    bj = &bj
                );
                let mut bind_ij = bij.parse::<Pattern<Math>>().unwrap().apply_one(
                    egraph,
                    eclass,
                    subst,
                    searcher_ast,
                    rule_name,
                );
                res.append(&mut bind_ij);

                let bji = format!(
                    "(b+ {j} {i} (l* (b- {aj} {ai} ?a) (b- {bj} {bi} ?b)))",
                    i = &i,
                    j = &j,
                    ai = &ai,
                    aj = &aj,
                    bi = &bi,
                    bj = &bj
                );
                let mut bind_ji = bji.parse::<Pattern<Math>>().unwrap().apply_one(
                    egraph,
                    eclass,
                    subst,
                    searcher_ast,
                    rule_name,
                );
                res.append(&mut bind_ji);
            } else {
                let i = a_schema.into_iter().next().unwrap_or(&wc).clone();
                let j = b_schema.into_iter().next().unwrap_or(&wc).clone();
                let mut mmul_ij = format!(
                    "(b+ {i} {j} (m* (b- {i} _ ?a) (b- _ {j} ?b)))",
                    i = &i,
                    j = &j
                )
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
                res.append(&mut mmul_ij);
            }
        }
        res
    }
}

#[derive(Debug)]
struct RABind;

impl Applier<Math, Meta> for RABind {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let e = subst["?e".parse::<egg::Var>().unwrap()];

        let mut res = Vec::new();
        if let Some(Schema::Schm(schema)) = egraph[e].data.schema.as_ref() {
            let mut schema = schema.keys();
            if schema.len() <= 2 {
                let wc = "_".to_owned();
                let i = schema.next().unwrap_or(&wc).clone();
                let j = schema.next().unwrap_or(&wc).clone();

                let mut bind_ij = format!("(b+ {i} {j} (b- {i} {j} ?e))", i = i, j = j)
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
                res.append(&mut bind_ij);

                let mut bind_ji = format!("(b+ {j} {i} (b- {j} {i} ?e))", i = i, j = j)
                    .parse::<Pattern<Math>>()
                    .unwrap()
                    .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
                res.append(&mut bind_ji);
            }
        }
        res
    }
}

#[derive(Debug)]
struct RARMMul;

impl Applier<Math, Meta> for RARMMul {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let a = subst["?a".parse::<egg::Var>().unwrap()];
        let b = subst["?b".parse::<egg::Var>().unwrap()];
        let mul = egraph.add(Math::RMMul([a, b]));
        let mul_schema: HashSet<_> = egraph[mul]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();
        let a_schema: HashSet<_> = egraph[a]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();
        let b_schema: HashSet<_> = egraph[b]
            .data
            .schema
            .as_ref()
            .unwrap()
            .get_schm()
            .keys()
            .collect();

        let wc = "_".to_owned();
        let i = a_schema
            .difference(&b_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();
        let k = b_schema
            .difference(&a_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();
        let j = a_schema
            .difference(&mul_schema)
            .cloned()
            .next()
            .unwrap_or(&wc)
            .clone();

        let mut res = vec![];
        let mut bind_ik = format!(
            "(b+ {i} {k} (m* (b- {i} {j} ?a) (b- {j} {k} ?b)))",
            i = &i,
            j = &j,
            k = &k
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        res.append(&mut bind_ik);

        let mut res = vec![];
        let mut bind_ik = format!(
            "(b+ {k} {i} (m* (b- {k} {j} ?b) (b- {j} {i} ?a)))",
            i = &i,
            j = &j,
            k = &k
        )
        .parse::<Pattern<Math>>()
        .unwrap()
        .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
        res.append(&mut bind_ik);

        res
    }
}

#[derive(Debug)]
struct RASum;

impl Applier<Math, Meta> for RASum {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Math, Meta>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<Math>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let i = subst["?i".parse::<egg::Var>().unwrap()];
        let x = subst["?x".parse::<egg::Var>().unwrap()];
        let i_s = egraph[i].data.schema.as_ref().unwrap().get_dims().0.clone();
        let sum = egraph.add(Math::Agg([i, x]));
        let mut schema = egraph[sum].data.schema.as_ref().unwrap().get_schm().keys();

        let mut res = vec![];
        if schema.len() <= 1 {
            let wc = "_".to_owned();
            let j = schema.next().unwrap_or(&wc).clone();

            let mut scol = format!("(b+ _ {j} (scol (b- {i} {j} ?x)))", j = &j, i = &i_s)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut scol);

            let mut srow = format!("(b+ {j} _ (srow (b- {j} {i} ?x)))", j = &j, i = &i_s)
                .parse::<Pattern<Math>>()
                .unwrap()
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name);
            res.append(&mut srow);
        }
        res
    }
}
