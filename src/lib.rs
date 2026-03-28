use egg::{
    define_language, DidMerge, Id, RecExpr, Rewrite,
};

use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::iter::*;
use std::time::Instant;

use ordered_float::NotNan;

use log::*;

mod translate;
pub use translate::Extractor;

mod hop;
pub use hop::*;

mod rules;
pub use rules::{rules, trans_rules, untrans_rules};

mod extract;
pub use extract::*;

pub type EGraph = egg::EGraph<Math, Meta>;

type Number = NotNan<f64>;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Meta;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaData {
    schema: Option<Schema>,
    sparsity: Option<NotNan<f64>>,
    nnz: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Schema {
    Schm(HashMap<String, usize>),
    Dims(String, usize),
    Name(String),
    Size(usize),
    Mat(usize, usize),
}

pub fn dag_cost(eg: &EGraph) -> usize {
    eg.classes()
        .map(|c| {
            let nnz = c.data.nnz;
            if let Some(Schema::Schm(_)) = c.data.schema {
                nnz.unwrap_or(get_vol(&c.data))
            } else {
                0
            }
        })
        .sum()
}

fn saturate(egraph: &mut EGraph, rws: &[Rewrite<Math, Meta>], iters: usize, _randomize: bool) {
    let limit = 8000000;
    let start_time = Instant::now();
    'outer: for i in 1..iters {
        info!("\n\nIteration {}\n", i);
        let mut applied = 0;
        for rw in rws {
            let ms = rw.search(egraph);
            if !ms.is_empty() {
                let new_ids = rw.apply(egraph, &ms);
                applied += new_ids.len();
            }
            if egraph.total_size() > limit {
                error!("Node limit exceeded. {} > {}", egraph.total_size(), limit);
                break 'outer;
            }
        }
        egraph.rebuild();
        info!(
            "Size: n={}, e={}",
            egraph.total_size(),
            egraph.number_of_classes()
        );
        if applied == 0 {
            info!("Stopping early!");
            break;
        }
    }
    info!("Rules time: {:?}", start_time.elapsed());
}

pub fn udf_meta(op: &str, children: &[&MetaData]) -> MetaData {
    match op {
        "axpy" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let _p = &children[1];
            let _p_schema = &children[1].schema.as_ref().unwrap();
            let y = &children[2];
            let y_schema = &children[2].schema.as_ref().unwrap();

            let (x_i, x_j) = x_schema.get_mat();
            let (_p_i, _p_j) = x_schema.get_mat();
            let (_y_i, _y_j) = y_schema.get_mat();

            let sparsity = x
                .sparsity
                .and_then(|x| y.sparsity.map(|y| min(1.0.into(), x + y)));

            let nnz = sparsity.map(|sp| {
                let vol: usize = x_i * x_j;
                let nnz = NotNan::from(vol as f64) * sp;
                nnz.round() as usize
            });

            let schema = Some(Schema::Mat(*x_i, *x_j));
            MetaData {
                schema,
                sparsity,
                nnz,
            }
        }
        "b(/)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let y = &children[1];
            let y_schema = &children[1].schema.as_ref().unwrap();

            let (x_i, x_j) = x_schema.get_mat();
            let (y_i, y_j) = y_schema.get_mat();
            dims_ok(*x_i, *x_j, *y_i, *y_j);
            let row = if *x_i == 1 { y_i } else { x_i };
            let col = if *x_j == 1 { y_j } else { x_j };

            let sparsity = min(x.sparsity, y.sparsity);

            let nnz = sparsity.map(|sp| {
                let vol: usize = *row * *col;
                let nnz = NotNan::from(vol as f64) * sp;
                nnz.round() as usize
            });

            MetaData {
                schema: Some(Schema::Mat(*row, *col)),
                nnz,
                sparsity,
            }
        }
        "m1mul" => {
            let x_schema = &children[0].schema.as_ref().unwrap();
            let y_schema = &children[1].schema.as_ref().unwrap();

            let (x_i, x_j) = x_schema.get_mat();
            let (y_i, y_j) = y_schema.get_mat();

            dims_ok(*x_i, *x_j, *y_i, *y_j);
            let row = if *x_i == 1 { y_i } else { x_i };
            let col = if *x_j == 1 { y_j } else { x_j };

            MetaData {
                schema: Some(Schema::Mat(*row, *col)),
                nnz: None,
                sparsity: None,
            }
        }
        "rix" => {
            // NOTE might want to tweak the nnz here
            let x = &children[0];
            let r = &children[5].schema.as_ref().unwrap();
            let row = r.get_size();
            let c = &children[6].schema.as_ref().unwrap();
            let col = c.get_size();
            MetaData {
                schema: Some(Schema::Mat(*row, *col)),
                nnz: x.nnz,
                sparsity: x.sparsity,
            }
        }
        "lix" => {
            // NOTE might want to tweak the nnz here
            let x = &children[0];
            let r = &children[6].schema.as_ref().unwrap();
            let row = r.get_size();
            let c = &children[7].schema.as_ref().unwrap();
            let col = c.get_size();
            MetaData {
                schema: Some(Schema::Mat(*row, *col)),
                nnz: x.nnz,
                sparsity: x.sparsity,
            }
        }
        "r(diag)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let (x_i, x_j) = x_schema.get_mat();

            let vol: Number = ((x_i * x_i * x_j * x_j) as f64).into();

            MetaData {
                schema: Some(Schema::Mat(x_i * x_j, x_i * x_j)),
                nnz: x.nnz,
                sparsity: x.sparsity.map(|sp| sp / vol),
            }
        }
        "u(ncol)" | "u(nrow)" => MetaData {
            schema: Some(Schema::Mat(1, 1)),
            nnz: Some(1),
            sparsity: Some(1.0.into()),
        },
        "ua(minR)" => {
            let x = &children[0];
            let x_schema = &children[0].schema.as_ref().unwrap();
            let (x_i, _x_j) = x_schema.get_mat();
            let sparsity = x.sparsity;
            let nnz = sparsity.map(|s| s.round() as usize * x_i);

            MetaData {
                schema: Some(Schema::Mat(*x_i, 1)),
                nnz,
                sparsity,
            }
        }
        // NOTE nnz here can be wrong
        "b(^)" | "b(min)" | "b(&)" | "u(sqrt)" | "b(!=)" | "b(==)" | "b(>)" | "b(>=)" | "b(<)"
        | "b(<=)" | "u(exp)" | "u(log)" | "sprop" | "selp" => {
            println!("got some");
            children[0].clone()
        }
        _ => panic!("Unknown udf {}", op),
    }
}

pub fn optimize(lgraph: EGraph, roots: Vec<Id>) -> Vec<RecExpr<Math>> {
    // Translate LA plan to RA
    println!("Translate LA plan to RA");
    let start_time = Instant::now();
    let (mut trans_graph, roots) = (lgraph, roots);
    saturate(&mut trans_graph, &trans_rules(), 27, false);
    let trans_ext = Extractor::new(&trans_graph, trans_model);
    let rplans: Vec<_> = roots.iter().map(|r| trans_ext.find_best(*r).expr).collect();
    let trans_time = start_time.elapsed();
    println!("TRANS TIME {:?}", trans_time);
    for rp in rplans.iter() {
        println!("{}", rp.pretty(80));
    }
    // Optimize RA plan
    println!("Optimize RA plan");
    let start_time = Instant::now();
    let mut opt_graph = EGraph::default();
    let opt_roots: Vec<_> = rplans.iter().map(|rp| opt_graph.add_expr(rp)).collect();
    let _orig_cost = dag_cost(&opt_graph);
    //println!("ROOT {:?}", opt_roots);
    saturate(&mut opt_graph, &rules(), 17, true);
    let sat_time = start_time.elapsed();
    println!("SAT TIME {:?}", sat_time);
    println!("DONE SATURATING");

    let start_time = Instant::now();
    let ext = Extractor::new(&opt_graph, trans_model);
    let bests = opt_roots.iter().map(|r| ext.find_best(*r).expr).collect();
    let solv_time = start_time.elapsed();
    println!("SOLVE TIME {:?}", solv_time);

    // let best = extract(opt_graph, &opt_roots);
    // for e in best.iter() {
    //     println!("{}", e.pretty(80));
    // }
    // // Translate RA plan to LA
    // println!("Translate RA plan to LA");
    // let mut untrans_graph = EGraph::default();
    // let untrans_roots: Vec<_> = best.iter().map(|p| {
    //     untrans_graph.add_expr(p)
    // }).collect();
    // let final_cost = dag_cost(&untrans_graph);
    // saturate(&mut untrans_graph, &untrans_rules(), 50, false);
    // let ext = Extractor::new(&untrans_graph, <Math as Language>::cost);
    // let bests = untrans_roots.iter().map(|r| {
    //     ext.find_best(*r).expr
    // }).collect();
    // println!("COST BEFORE {}", orig_cost);
    // println!("COST AFTER {}", final_cost);
    // println!("SPEEDUP {}", final_cost as f64 / orig_cost as f64);
    bests
}

impl Schema {
    pub fn get_schm(&self) -> &HashMap<String, usize> {
        if let Self::Schm(s) = self {
            s
        } else {
            panic!("cannot get schm")
        }
    }

    pub fn get_dims(&self) -> (&String, &usize) {
        if let Self::Dims(i, n) = self {
            (i, n)
        } else {
            panic!("cannot get dims")
        }
    }

    pub fn get_name(&self) -> &String {
        if let Self::Name(n) = self {
            n
        } else {
            panic!("cannot get name")
        }
    }

    pub fn get_size(&self) -> &usize {
        if let Self::Size(s) = self {
            s
        } else {
            panic!("cannot get size")
        }
    }

    pub fn get_mat(&self) -> (&usize, &usize) {
        if let Self::Mat(i, j) = self {
            (i, j)
        } else {
            panic!("cannot get mat")
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        if let (Self::Schm(s1), Self::Schm(s2)) = (self, other) {
            let mut res = s1.clone();
            res.extend(s2.clone());
            Self::Schm(res)
        } else {
            panic!("unioning a non-schema")
        }
    }
}

impl egg::Analysis<Math> for Meta {
    type Data = MetaData;

    fn modify(_egraph: &mut EGraph, _id: Id) {}
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let sparsity = [a.sparsity, b.sparsity]
            .iter()
            .flatten()
            .min()
            .copied();
        let nnz = [a.nnz, b.nnz].iter().flatten().min().copied();
        debug_assert_eq!(&a.schema, &b.schema);
        let schema = a.schema.clone();
        // NOTE perhaps move the special case for 0 to
        // make(Mul)?
        // match (&sparsity, &nnz)  {
        //    (Some(f), Some(0)) if *f == 0.0.into() => {
        //            Some(Schema::Schm(HashMap::new()))
        //    },
        //    _ => {
        //        debug_assert_eq!(&self.schema, &other.schema);
        //        self.schema.clone()
        //    }
        //};
        let new = MetaData {
            schema,
            sparsity,
            nnz,
        };
        let did_merge = DidMerge(a != &new, b != new);
        *a = new;
        did_merge
    }

    fn make(egraph: &mut EGraph, enode: &Math, _id: Id) -> Self::Data {
        use Math::*;
        let egraph: &EGraph = egraph;
        // Helper: get analysis data for a child id
        let d = |id: &Id| &egraph[*id].data;
        // Helper: get schema for a child id (panics if None)
        let schm = |id: &Id| d(id).schema.as_ref().unwrap();
        match enode {
            Ind([x, y]) | Add([x, y]) | Mul([x, y]) => {
                let (xd, yd) = (d(x), d(y));
                let mut s = xd.schema.as_ref().unwrap().get_schm().clone();
                s.extend(yd.schema.as_ref().unwrap().get_schm().clone());
                let sparsity = match enode {
                    Add(..) => xd.sparsity.and_then(|a| yd.sparsity.map(|b| min(1.0.into(), a + b))),
                    _ => min(xd.sparsity, yd.sparsity),
                };
                let nnz = sparsity.map(|sp| {
                    let vol: usize = s.values().product();
                    (NotNan::from(vol as f64) * sp).round() as usize
                });
                MetaData { schema: Some(Schema::Schm(s)), sparsity, nnz }
            }
            Agg([dim, body]) => {
                let k = schm(dim).get_dims().0.clone();
                let bd = d(body);
                let mut body_schm = bd.schema.as_ref().unwrap().get_schm().clone();
                body_schm.remove(&k);
                let vol: usize = body_schm.values().product();
                let sparsity = bd.nnz.map(|nnz| min(1.0.into(), NotNan::from(nnz as f64 / vol as f64)));
                let nnz = bd.nnz.map(|z| min(vol, z));
                MetaData { schema: Some(Schema::Schm(body_schm)), sparsity, nnz }
            }
            RMMul([x, y]) => {
                let mut xs = d(x).schema.as_ref().unwrap().get_schm().clone();
                let x_keys: HashSet<_> = xs.keys().cloned().collect();
                let ys = d(y).schema.as_ref().unwrap().get_schm().clone();
                let y_keys: HashSet<_> = ys.keys().cloned().collect();
                let j = x_keys.intersection(&y_keys).next().unwrap().clone();
                xs.extend(ys);
                xs.remove(&j);
                let vol: usize = xs.values().product();
                MetaData { schema: Some(Schema::Schm(xs)), sparsity: Some(1.0.into()), nnz: Some(vol) }
            }
            Lit([num]) => {
                let nd = d(num);
                MetaData { schema: Some(Schema::Schm(HashMap::default())), sparsity: nd.sparsity, nnz: nd.nnz }
            }
            Mat([_x, i_dim, j_dim, nnz_id]) => {
                let (i, n) = { let s = schm(i_dim).get_dims(); (s.0.clone(), *s.1) };
                let (j, m) = { let s = schm(j_dim).get_dims(); (s.0.clone(), *s.1) };
                let nnz = d(nnz_id).nnz;
                let mut s = HashMap::new();
                if n != 1 { s.insert(i, n); }
                if m != 1 { s.insert(j, m); }
                MetaData {
                    schema: Some(Schema::Schm(s)),
                    nnz,
                    sparsity: Some(NotNan::from(nnz.unwrap() as f64 / (n * m) as f64)),
                }
            }
            Dim([name_id, size_id]) => {
                let name = schm(name_id).get_name().clone();
                let size = *schm(size_id).get_size();
                MetaData { schema: Some(Schema::Dims(name, size)), nnz: None, sparsity: None }
            }
            Sub([e, v, body]) => {
                let (e_i, e_n) = { let s = schm(e).get_dims(); (s.0.clone(), *s.1) };
                let (v_i, v_n) = { let s = schm(v).get_dims(); (s.0.clone(), *s.1) };
                debug_assert_eq!(e_n, v_n, "substituting for different size");
                let (body_schm, body_nnz, body_sp) = {
                    let bd = d(body);
                    (bd.schema.clone(), bd.nnz, bd.sparsity)
                };
                let new_schema = match body_schm.as_ref().unwrap() {
                    Schema::Schm(s) => {
                        let mut res = s.clone();
                        if let Some(m) = res.remove(&v_i) { res.insert(e_i, m); }
                        Schema::Schm(res)
                    }
                    Schema::Dims(body_i, body_n) => {
                        if *body_i == v_i { Schema::Dims(e_i, e_n) }
                        else { Schema::Dims(body_i.clone(), *body_n) }
                    }
                    Schema::Size(n) => panic!("cannot subst for size {:?}", n),
                    _ => panic!("cannot subst for attr. and mat"),
                };
                MetaData { schema: Some(new_schema), nnz: body_nnz, sparsity: body_sp }
            }
            Var([_]) => MetaData {
                schema: Some(Schema::Schm(HashMap::default())),
                nnz: Some(1),
                sparsity: Some(1.0.into()),
            },
            Num(n) => MetaData {
                schema: Some(Schema::Size((*n).max(0) as usize)),
                nnz: Some(if *n == 0 { 0 } else { 1 }),
                sparsity: Some(if *n == 0 { 0.0.into() } else { 1.0.into() }),
            },
            Nnz([n]) => MetaData { schema: None, nnz: Some(*schm(n).get_size()), sparsity: None },
            Str(s) => MetaData {
                schema: Some(Schema::Name(s.clone())),
                nnz: Some(1),
                sparsity: Some(1.0.into()),
            },
            Udf([op_id, arg_id]) => {
                let op_s = schm(op_id).get_name().clone();
                let arg_data = d(arg_id);
                udf_meta(&op_s, &[arg_data])
            }
            LMat([_x, row, col, nnz_id]) => {
                let row_sz = *schm(row).get_size();
                let col_sz = *schm(col).get_size();
                let nnz = d(nnz_id).nnz;
                MetaData { schema: Some(Schema::Mat(row_sz, col_sz)), nnz, sparsity: None }
            }
            LMin([x, y]) | LAdd([x, y]) | LMul([x, y]) => {
                let (x_i, x_j) = { let s = schm(x).get_mat(); (*s.0, *s.1) };
                let (y_i, y_j) = { let s = schm(y).get_mat(); (*s.0, *s.1) };
                dims_ok(x_i, x_j, y_i, y_j);
                let row = if x_i == 1 { y_i } else { x_i };
                let col = if x_j == 1 { y_j } else { x_j };
                MetaData { schema: Some(Schema::Mat(row, col)), nnz: None, sparsity: None }
            }
            MMul([x, y]) => {
                let (x_i, x_j) = { let s = schm(x).get_mat(); (*s.0, *s.1) };
                let (y_i, y_j) = { let s = schm(y).get_mat(); (*s.0, *s.1) };
                debug_assert_eq!(x_j, y_i, "wrong dimensions in mmul");
                MetaData { schema: Some(Schema::Mat(x_i, y_j)), nnz: None, sparsity: None }
            }
            LTrs([a]) => {
                let (x_i, x_j) = { let s = schm(a).get_mat(); (*s.0, *s.1) };
                MetaData { schema: Some(Schema::Mat(x_j, x_i)), nnz: None, sparsity: None }
            }
            Srow([a]) => {
                let x_i = *schm(a).get_mat().0;
                MetaData { schema: Some(Schema::Mat(x_i, 1)), nnz: None, sparsity: None }
            }
            Scol([a]) => {
                let x_j = *schm(a).get_mat().1;
                MetaData { schema: Some(Schema::Mat(1, x_j)), nnz: None, sparsity: None }
            }
            Sall([_]) => MetaData { schema: Some(Schema::Mat(1, 1)), nnz: None, sparsity: None },
            Bind([i, j, x]) => {
                let i_name = schm(i).get_name().clone();
                let j_name = schm(j).get_name().clone();
                let (x_row, x_col) = { let s = schm(x).get_mat(); (*s.0, *s.1) };
                let (x_nnz, x_sp) = { let xd = d(x); (xd.nnz, xd.sparsity) };
                let mut s = HashMap::new();
                if x_row != 1 { s.insert(i_name, x_row); }
                if x_col != 1 { s.insert(j_name, x_col); }
                MetaData { schema: Some(Schema::Schm(s)), nnz: x_nnz, sparsity: x_sp }
            }
            Ubnd([i, j, x]) => {
                let i_name = schm(i).get_name().clone();
                let j_name = schm(j).get_name().clone();
                let x_schm = schm(x).get_schm().clone();
                let (x_nnz, x_sp) = { let xd = d(x); (xd.nnz, xd.sparsity) };
                let row = *x_schm.get(&i_name).unwrap_or(&1);
                let col = *x_schm.get(&j_name).unwrap_or(&1);
                MetaData { schema: Some(Schema::Mat(row, col)), nnz: x_nnz, sparsity: x_sp }
            }
            LLit([_]) => MetaData { schema: Some(Schema::Mat(1, 1)), nnz: None, sparsity: None },
            TWrite(_) => MetaData { schema: None, nnz: None, sparsity: None },
        }
    }
}

fn dims_ok(x_i: usize, x_j: usize, y_i: usize, y_j: usize) {
    debug_assert!(
        (x_i == y_i && x_j == y_j)
            || (x_i == y_i && y_j == 1)
            || (x_i == y_i && x_j == 1)
            || (x_i == 1 && x_j == y_j)
            || (y_i == 1 && x_j == y_j)
            || (x_i == 1 && x_j == 1)
            || (y_i == 1 && y_j == 1),
        "{:?}", (x_i, x_j, y_i, y_j)
    );
}

define_language! {
    pub enum Math {
        // LA
        "lmat" = LMat([Id; 4]) ,
        "l+" = LAdd([Id; 2]) ,
        "l-" = LMin([Id; 2]) ,
        "l*" = LMul([Id; 2]) ,
        "m*" = MMul([Id; 2]) ,
        "trans" = LTrs([Id; 1]) ,
        "srow" = Srow([Id; 1]) ,
        "scol" = Scol([Id; 1]) ,
        "sall" = Sall([Id; 1]) ,
        "b+" = Bind([Id; 3]) ,
        "b-" = Ubnd([Id; 3]) ,
        "llit" = LLit([Id; 1]) ,
        "udf" = Udf([Id; 2]) ,
        // RA
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "sum" = Agg([Id; 2]),
        "rm*" = RMMul([Id; 2]),
        "lit" = Lit([Id; 1]),
        "var" = Var([Id; 1]),
        "mat" = Mat([Id; 4]),
        "dim" = Dim([Id; 2]),
        "nnz" = Nnz([Id; 1]),
        "subst" = Sub([Id; 3]),
        "ind" = Ind([Id; 2]),
        Num(i32),
        Str(String),
        // NOTE careful here, TWrite might be parsed as Str
        TWrite(String),
    }
}

// Cost to translate to LA
// TODO twrite?
// impl Language for Math {
//     fn cost(&self, children: &[f64]) -> f64 {
//         use Math::*;
//         let cost = match self {
//             LMat | LAdd | LMin | LMul | MMul | LTrs | Srow | Scol | Sall | LLit | Udf | Num(_)
//             | Str(_) => 1.0,
//             _ => 100.0,
//         };
//         cost + children.iter().sum::<f64>()
//     }
// }

// Cost to translation to RA
// TODO twrite?
fn trans_model(op: &Math, children: &[f64]) -> f64 {
    use Math::*;
    let cost = match op {
        LMat(..) | LAdd(..) | LMin(..) | LMul(..) | MMul(..) | LTrs(..) | Srow(..) | Scol(..)
        | Sall(..) | LLit(..) | Sub(..) => 100.0,
        Bind(..) | Ubnd(..) => 10.0,
        _ => 1.0,
    };
    let c_cost: f64 = children.iter().sum();
    cost + c_cost
}

pub fn get_vol(m: &MetaData) -> usize {
    if let Some(schm) = &m.schema {
        match schm {
            Schema::Schm(s) => s.values().product(),
            Schema::Mat(r, c) => r * c,
            _ => 0,
        }
    } else {
        0
    }
}
