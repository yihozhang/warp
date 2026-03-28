use crate::{Math, EGraph};
use std::collections::HashMap;
use egg::{Id, Language, RecExpr};

pub static HOP: &str = "29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;";

#[derive(Debug)]
enum HopOp {
    Num(f64),
    Var(String),
    Write(String),
    Udf(String),
    Op(String),
}

#[derive(Debug)]
pub struct Hop {
    id: u32,
    op: HopOp,
    children: Vec<u32>,
    row: u32,
    col: u32,
    nnz: Option<i32>,
}

fn parse_op(s: &str) -> HopOp {
    match s {
        "r(t)" | "b(*)" | "b(+)" | "b(-)" | "ba(+*)" | "ua(+R)" | "ua(+C)" | "ua(+RC)" => {
            HopOp::Op(s.to_owned())
        }
        _ if s.starts_with("LiteralOp") => {
            let n: f64 = s.split_whitespace().nth(1).unwrap().parse().unwrap();
            HopOp::Num(n)
        }
        _ if s.starts_with("TRead") => {
            let v = s.split_whitespace().nth(1).unwrap();
            HopOp::Var(v.to_owned())
        }
        _ if s.starts_with("TWrite") => {
            let v = s.split_whitespace().nth(1).unwrap();
            HopOp::Write(v.to_owned())
        }
        _ => HopOp::Udf(s.to_owned()),
    }
}

pub fn parse_hop(s: &str) -> Hop {
    let hop: Vec<_> = s.split(";").collect();
    let id: u32 = hop[1].parse().unwrap();
    let op_s = hop[2];
    let op = parse_op(op_s);
    let children: Vec<u32> = hop[3].split(",").filter_map(|s| s.parse().ok()).collect();

    let meta: Vec<Option<i32>> = hop[4].split(",").map(|s| s.parse().ok()).collect();
    let mut row = meta[0].unwrap_or(0);
    if row == 0 || row == -1 { row = 1 };
    let mut col = meta[1].unwrap_or(0);
    if col == 0 || col == -1 { col = 1 };
    let mut nnz = meta[4];
    if let Some(-1) = nnz {
        nnz = Some(row as i32 * col as i32)
    }

    Hop { id, op, children, row: row as u32, col: col as u32, nnz }
}

fn build_la_math(op_str: &str, children: &[Id]) -> Math {
    use Math::*;
    match op_str {
        "r(t)"    => LTrs([children[0]]),
        "b(*)"    => LMul([children[0], children[1]]),
        "b(+)"    => LAdd([children[0], children[1]]),
        "b(-)"    => LMin([children[0], children[1]]),
        "ba(+*)"  => MMul([children[0], children[1]]),
        "ua(+R)"  => Srow([children[0]]),
        "ua(+C)"  => Scol([children[0]]),
        "ua(+RC)" => Sall([children[0]]),
        _ => panic!("unknown LA op: {}", op_str),
    }
}

pub fn load_dag(egraph: &mut EGraph, s: &str) -> Vec<Id> {
    let mut id_map: HashMap<u32, Id> = HashMap::new();
    let hops = s.lines();
    let mut roots = vec![];
    for h in hops {
        let hop = parse_hop(h);
        match hop.op {
            HopOp::Num(n) => {
                let expr_s = format!("(llit {})", n as i32);
                let exp: RecExpr<Math> = expr_s.parse().unwrap();
                let lit = egraph.add_expr(&exp);
                id_map.insert(hop.id, lit);
            }
            HopOp::Var(x) => {
                let m = format!("(lmat {x} {i} {j} {z})",
                    x = x, i = hop.row, j = hop.col, z = hop.nnz.unwrap());
                let exp: RecExpr<Math> = m.parse().unwrap();
                let mat = egraph.add_expr(&exp);
                id_map.insert(hop.id, mat);
            }
            HopOp::Write(x) => {
                // TWrite is a leaf in the current language definition; child connection is lost.
                let id = egraph.add(Math::TWrite(x));
                roots.push(id);
                id_map.insert(hop.id, id);
            }
            HopOp::Udf(x) => {
                let children: Vec<Id> = hop.children.iter().map(|c| id_map[c]).collect();
                let op_id = egraph.add(Math::Str(x));
                let arg_id = if children.is_empty() { op_id } else { children[0] };
                let udf = egraph.add(Math::Udf([op_id, arg_id]));
                id_map.insert(hop.id, udf);
            }
            HopOp::Op(s) => {
                let children: Vec<Id> = hop.children.iter().map(|c| id_map[c]).collect();
                let math = build_la_math(&s, &children);
                let id = egraph.add(math);
                id_map.insert(hop.id, id);
            }
        }
    }
    roots
}

pub fn print_dag(egraph: &EGraph) {
    use Math::*;
    for c in egraph.classes() {
        let id = &c.id;
        for e in &c.nodes {
            match e {
                Str(_) | Num(_) => {}
                Udf([op_id, arg_id]) => {
                    print!("0,0;{id};", id = id);
                    let op = format!("{}", &egraph[*op_id].nodes[0]);
                    print!("{};", op);
                    print!("{},", arg_id);
                    println!(";;M;D;;;;;");
                }
                LMat([name_id, _, _, _]) => {
                    print!("0,0;{id};TRead ", id = id);
                    print!("{}", &egraph[*name_id].nodes[0]);
                    println!(";;;M;D;;;;;");
                }
                LLit([val_id]) => {
                    print!("0,0;{id};LiteralOp ", id = id);
                    print!("{}", &egraph[*val_id].nodes[0]);
                    println!(";;;M;D;;;;;");
                }
                TWrite(s) => {
                    println!("0,0;{id};TWrite {var};;;M;D;;;;;", id = id, var = s);
                }
                Var([_]) => {
                    println!("var");
                }
                e => {
                    print!("0,0;{id};{op};", id = id, op = dml_op(e));
                    for c in e.children() {
                        print!("{},", c);
                    }
                    println!(";;M;D;;;;;");
                }
            }
        }
    }
}

fn dml_op(op: &Math) -> &'static str {
    use Math::*;
    match op {
        LAdd(..) => "b(+)",
        LMin(..) => "b(-)",
        LMul(..) => "b(*)",
        MMul(..) => "ba(+*)",
        LTrs(..) => "r(t)",
        Srow(..) => "ua(+R)",
        Scol(..) => "ua(+C)",
        Sall(..) => "ua(+RC)",
        o => {
            println!("UNK {}", o);
            "UNKNOWN OP"
        }
    }
}

// 29,29;86;TRead B;;500000,10,1000,1000,5000000;M;D;0,0,38,-;;;

// 29,29;80;LiteralOp 6.14;;0,0,-1,-1,-1;S;D;0,0,0,0;;;
// LMat = "lmat", LLit = "llit", Udf = "udf", Var = "var"
