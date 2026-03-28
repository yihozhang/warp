use egg::{Analysis, EClass, EGraph, Id, Language, RecExpr};

use indexmap::IndexMap;
use std::cmp::Ordering;

pub type Cost = f64;

pub struct CostExpr<L: Language> {
    pub cost: Cost,
    pub expr: RecExpr<L>,
}

pub struct Extractor<'a, L: Language, M: Analysis<L>> {
    costs: IndexMap<Id, Cost>,
    egraph: &'a EGraph<L, M>,
    model: fn(&L, &[Cost]) -> Cost,
}

fn cmp(a: &Option<Cost>, b: &Option<Cost>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(&b).unwrap(),
    }
}

impl<'a, L: Language, M: Analysis<L>> Extractor<'a, L, M> {
    pub fn new(egraph: &'a EGraph<L, M>, model: fn(&L, &[Cost]) -> Cost) -> Self {
        let costs = IndexMap::default();
        let mut extractor = Extractor {
            costs,
            egraph,
            model,
        };
        extractor.find_costs();

        extractor
    }

    pub fn calculate_cost(&self, expr: &RecExpr<L>) -> Cost {
        let mut costs: Vec<Cost> = Vec::with_capacity(expr.as_ref().len());
        for node in expr.as_ref() {
            let child_costs: Vec<_> = node
                .children()
                .iter()
                .map(|id| costs[usize::from(*id)])
                .collect();
            costs.push((self.model)(node, &child_costs));
        }
        costs.last().copied().unwrap_or(0.0)
    }

    pub fn find_best(&self, eclass: Id) -> CostExpr<L> {
        let expr = self.find_best_expr(eclass);
        let cost = self.calculate_cost(&expr);
        CostExpr { cost, expr }
    }

    fn find_best_expr(&self, eclass: Id) -> RecExpr<L> {
        fn build_best_expr<L: Language, M: Analysis<L>>(
            extractor: &Extractor<'_, L, M>,
            eclass: Id,
            expr: &mut RecExpr<L>,
        ) -> Id {
            let eclass = extractor.egraph.find(eclass);

            let best_node = extractor.egraph[eclass]
                .iter()
                .filter(|n| extractor.node_total_cost(n).is_some())
                .min_by(|a, b| {
                    let a = extractor.node_total_cost(a);
                    let b = extractor.node_total_cost(b);
                    cmp(&a, &b)
                })
                .expect("eclass shouldn't be empty");

            let node = best_node
                .clone()
                .map_children(|child| build_best_expr(extractor, child, expr));
            expr.add(node)
        }

        let mut expr = RecExpr::default();
        build_best_expr(self, eclass, &mut expr);
        expr
    }

    fn node_total_cost(&self, node: &L) -> Option<Cost> {
        let child_costs: Option<Vec<_>> = node
            .children()
            .iter()
            .map(|id| self.costs.get(id).cloned())
            .collect();
        let cost = (self.model)(node, &child_costs?);
        Some(cost)
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                match (self.costs.get(&class.id), self.make_pass(class)) {
                    (None, Some(cost)) => {
                        self.costs.insert(class.id, cost);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new < *old => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }
    }

    fn make_pass(&self, eclass: &EClass<L, <M as Analysis<L>>::Data>) -> Option<Cost> {
        eclass
            .iter()
            .map(|n| self.node_total_cost(n))
            .min_by(cmp)
            .unwrap()
    }
}
