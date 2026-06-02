use std::fmt;

const NIL: i64 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    R,
    B,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Color::R => write!(f, "R"),
            Color::B => write!(f, "B"),
        }
    }
}

impl Color {
    fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "R" => Ok(Color::R),
            "B" => Ok(Color::B),
            other => Err(format!("invalid color: {other}")),
        }
    }

    fn is_black(self) -> bool {
        matches!(self, Color::B)
    }

    fn is_red(self) -> bool {
        matches!(self, Color::R)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RBNode {
    key: i64,
    color: Color,
    left: i64,
    right: i64,
    bh: i64,
}

impl RBNode {
    fn nil() -> Self {
        Self {
            key: 0,
            color: Color::B,
            left: NIL,
            right: NIL,
            bh: 0,
        }
    }
}

pub struct RBTree {
    nodes: Vec<RBNode>,
    root: i64,
    max_nodes: i64,
}

impl RBTree {
    pub fn new(max_nodes: i64) -> Self {
        let mut nodes = Vec::with_capacity((max_nodes + 1) as usize);
        for _ in 0..=max_nodes {
            nodes.push(RBNode::nil());
        }
        Self {
            nodes,
            root: NIL,
            max_nodes,
        }
    }

    pub fn reset(&mut self) {
        for i in 0..self.nodes.len() {
            self.nodes[i] = RBNode::nil();
        }
        self.root = NIL;
    }

    pub fn set_state(
        &mut self,
        node_records: &[(i64, i64, String, i64, i64, i64)],
        new_root: i64,
    ) -> Result<(), String> {
        self.reset();
        let max_id = node_records
            .iter()
            .map(|(id, _, _, _, _, _)| *id)
            .max()
            .unwrap_or(0);
        self.nodes.resize((max_id + 1) as usize, RBNode::nil());
        for &(id, key, ref color_str, left, right, bh) in node_records {
            let color = Color::from_str(color_str)?;
            self.nodes[id as usize] = RBNode {
                key,
                color,
                left,
                right,
                bh,
            };
        }
        self.root = new_root;
        Ok(())
    }

    pub fn insert(&mut self, key: i64) -> Result<(), String> {
        if self.root == NIL {
            let id = self.alloc_node()?;
            self.nodes[id as usize] = RBNode {
                key,
                color: Color::B,
                left: NIL,
                right: NIL,
                bh: 1,
            };
            self.root = id;
            return Ok(());
        }

        if self.find_node(key).is_some() {
            return Ok(());
        }

        let new_id = self.alloc_node()?;
        self.nodes[new_id as usize] = RBNode {
            key,
            color: Color::R,
            left: NIL,
            right: NIL,
            bh: 0,
        };

        let parent_id = self.bst_insert_parent(self.root, key)?;
        if key < self.nodes[parent_id as usize].key {
            self.nodes[parent_id as usize].left = new_id;
        } else {
            self.nodes[parent_id as usize].right = new_id;
        }

        self.fixup_after_insert(new_id)?;

        self.nodes[self.root as usize].color = Color::B;
        self.recompute_black_heights()?;
        Ok(())
    }

    pub fn check_invariants(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        if self.nodes[NIL as usize] != RBNode::nil() {
            errors.push("NilInv violated: NIL node is not NilRec".into());
        }

        if self.root != NIL && !self.nodes[self.root as usize].color.is_black() {
            errors.push("RootBlack violated: root is not black".into());
        }

        for id in 1..self.nodes.len() as i64 {
            let node = &self.nodes[id as usize];
            if node.key == 0 {
                continue;
            }
            if node.color.is_red() {
                if node.left != NIL && self.nodes[node.left as usize].color.is_red() {
                    errors.push(format!(
                        "NoDoubleRed violated: node {id} (red) has red left child {}",
                        node.left
                    ));
                }
                if node.right != NIL && self.nodes[node.right as usize].color.is_red() {
                    errors.push(format!(
                        "NoDoubleRed violated: node {id} (red) has red right child {}",
                        node.right
                    ));
                }
            }

            if node.left != NIL
                && self.nodes[node.left as usize].key != 0
                && self.nodes[node.left as usize].key >= node.key
            {
                errors.push(format!(
                    "BSTInv violated: node {id} (key={}) has left child {} (key={})",
                    node.key,
                    node.left,
                    self.nodes[node.left as usize].key
                ));
            }
            if node.right != NIL
                && self.nodes[node.right as usize].key != 0
                && self.nodes[node.right as usize].key <= node.key
            {
                errors.push(format!(
                    "BSTInv violated: node {id} (key={}) has right child {} (key={})",
                    node.key,
                    node.right,
                    self.nodes[node.right as usize].key
                ));
            }
        }

        for id in 1..self.nodes.len() as i64 {
            let node = &self.nodes[id as usize];
            if node.key == 0 {
                continue;
            }
            let lbh = self.nodes[node.left as usize].bh;
            let rbh = self.nodes[node.right as usize].bh;
            if lbh != rbh {
                errors.push(format!(
                    "BHInv violated: node {id} has left bh={lbh}, right bh={rbh}"
                ));
            }
            let expected_bh = lbh + if node.color.is_black() { 1 } else { 0 };
            if node.bh != expected_bh {
                errors.push(format!(
                    "BHInv violated: node {id} has bh={} but expected {expected_bh}",
                    node.bh
                ));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn node_count(&self) -> usize {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(id, n)| *id as i64 != NIL && n.key != 0)
            .count()
    }

    pub fn root(&self) -> i64 {
        self.root
    }

    pub fn nodes(&self) -> &Vec<RBNode> {
        &self.nodes
    }

    pub fn nodes_mut(&mut self) -> &mut Vec<RBNode> {
        &mut self.nodes
    }

    pub fn nodes_sorted(&self) -> Vec<(i64, i64, String, i64, i64, i64)> {
        let mut result = Vec::new();
        for (id, node) in self.nodes.iter().enumerate() {
            let id = id as i64;
            result.push((
                id,
                node.key,
                node.color.to_string(),
                node.left,
                node.right,
                node.bh,
            ));
        }
        result.sort_by_key(|(id, _, _, _, _, _)| *id);
        result
    }

    fn alloc_node(&mut self) -> Result<i64, String> {
        for id in 1..=self.max_nodes as usize {
            if self.nodes[id].key == 0 {
                return Ok(id as i64);
            }
        }
        Err(format!("max_nodes ({}) exceeded", self.max_nodes))
    }

    fn find_node(&self, key: i64) -> Option<i64> {
        let mut cur = self.root;
        while cur != NIL {
            let node_key = self.nodes[cur as usize].key;
            if node_key == 0 {
                return None;
            }
            match key.cmp(&node_key) {
                std::cmp::Ordering::Equal => return Some(cur),
                std::cmp::Ordering::Less => cur = self.nodes[cur as usize].left,
                std::cmp::Ordering::Greater => cur = self.nodes[cur as usize].right,
            }
        }
        None
    }

    fn bst_insert_parent(&self, root: i64, key: i64) -> Result<i64, String> {
        let mut cur = root;
        let mut parent = NIL;
        while cur != NIL {
            parent = cur;
            let node_key = self.nodes[cur as usize].key;
            if node_key == 0 {
                return Err("encountered nil node during BST insert".into());
            }
            if key < node_key {
                cur = self.nodes[cur as usize].left;
            } else {
                cur = self.nodes[cur as usize].right;
            }
        }
        if parent == NIL {
            return Err("BST insert failed to find parent".into());
        }
        Ok(parent)
    }

    fn fixup_after_insert(&mut self, mut z: i64) -> Result<(), String> {
        loop {
            let parent = self.parent_of(z)?;
            if parent == NIL || self.nodes[parent as usize].color.is_black() {
                break;
            }
            let grandparent = self.parent_of(parent)?;
            if grandparent == NIL {
                break;
            }

            let parent_is_left = self.nodes[grandparent as usize].left == parent;
            let uncle = if parent_is_left {
                self.nodes[grandparent as usize].right
            } else {
                self.nodes[grandparent as usize].left
            };

            let uncle_is_red = uncle != NIL && self.nodes[uncle as usize].color.is_red();

            if uncle_is_red {
                self.nodes[parent as usize].color = Color::B;
                self.nodes[grandparent as usize].color = Color::R;
                z = grandparent;
            } else if parent_is_left {
                if z == self.nodes[parent as usize].right {
                    self.rotate_left(parent);
                    z = parent;
                }
                let p = self.parent_of(z)?;
                let gp = self.parent_of(p)?;
                if gp != NIL {
                    let p_idx = p;
                    let gp_idx = gp;
                    self.nodes[p_idx as usize].color = Color::B;
                    self.nodes[gp_idx as usize].color = Color::R;
                    self.rotate_right(gp_idx);
                }
            } else {
                if z == self.nodes[parent as usize].left {
                    self.rotate_right(parent);
                    z = parent;
                }
                let p = self.parent_of(z)?;
                let gp = self.parent_of(p)?;
                if gp != NIL {
                    let p_idx = p;
                    let gp_idx = gp;
                    self.nodes[p_idx as usize].color = Color::B;
                    self.nodes[gp_idx as usize].color = Color::R;
                    self.rotate_left(gp_idx);
                }
            }
        }
        self.nodes[self.root as usize].color = Color::B;
        Ok(())
    }

    fn parent_of(&self, id: i64) -> Result<i64, String> {
        if id == self.root {
            return Ok(NIL);
        }
        let key = self.nodes[id as usize].key;
        let mut cur = self.root;
        let mut parent = NIL;
        while cur != NIL {
            if cur == id {
                return Ok(parent);
            }
            parent = cur;
            let node_key = self.nodes[cur as usize].key;
            if node_key == 0 {
                return Err(format!("node {id} not found in tree"));
            }
            if key < node_key {
                cur = self.nodes[cur as usize].left;
            } else {
                cur = self.nodes[cur as usize].right;
            }
        }
        Err(format!("node {id} not found in tree"))
    }

    fn rotate_left(&mut self, x: i64) {
        let y = self.nodes[x as usize].right;
        if y == NIL {
            return;
        }
        self.nodes[x as usize].right = self.nodes[y as usize].left;
        if self.nodes[y as usize].left != NIL {
            // left child's parent implicitly updated through tree structure
        }
        let p = if x == self.root {
            NIL
        } else {
            self.find_parent_id(x)
        };
        self.nodes[y as usize].left = x;
        if p == NIL {
            self.root = y;
        } else if self.nodes[p as usize].left == x {
            self.nodes[p as usize].left = y;
        } else {
            self.nodes[p as usize].right = y;
        }
    }

    fn rotate_right(&mut self, x: i64) {
        let y = self.nodes[x as usize].left;
        if y == NIL {
            return;
        }
        self.nodes[x as usize].left = self.nodes[y as usize].right;
        let p = if x == self.root {
            NIL
        } else {
            self.find_parent_id(x)
        };
        self.nodes[y as usize].right = x;
        if p == NIL {
            self.root = y;
        } else if self.nodes[p as usize].left == x {
            self.nodes[p as usize].left = y;
        } else {
            self.nodes[p as usize].right = y;
        }
    }

    fn find_parent_id(&self, id: i64) -> i64 {
        let key = self.nodes[id as usize].key;
        let mut cur = self.root;
        let mut parent = NIL;
        while cur != NIL {
            if cur == id {
                return parent;
            }
            parent = cur;
            let node_key = self.nodes[cur as usize].key;
            if node_key == 0 {
                return NIL;
            }
            if key < node_key {
                cur = self.nodes[cur as usize].left;
            } else {
                cur = self.nodes[cur as usize].right;
            }
        }
        NIL
    }

    fn recompute_black_heights(&mut self) -> Result<(), String> {
        self.recompute_bh_rec(self.root)?;
        Ok(())
    }

    fn recompute_bh_rec(&mut self, id: i64) -> Result<i64, String> {
        if id == NIL {
            return Ok(0);
        }
        if self.nodes[id as usize].key == 0 {
            return Ok(0);
        }
        let lbh = self.recompute_bh_rec(self.nodes[id as usize].left)?;
        let rbh = self.recompute_bh_rec(self.nodes[id as usize].right)?;
        if lbh != rbh {
            return Err(format!("BH mismatch at node {id}: left={lbh}, right={rbh}"));
        }
        let add = if self.nodes[id as usize].color.is_black() {
            1
        } else {
            0
        };
        self.nodes[id as usize].bh = lbh + add;
        Ok(lbh + add)
    }

    fn successor(&self, id: i64) -> Option<i64> {
        let right = self.nodes[id as usize].right;
        if right == NIL {
            return None;
        }
        let mut cur = right;
        while self.nodes[cur as usize].left != NIL {
            cur = self.nodes[cur as usize].left;
        }
        Some(cur)
    }

    fn transplant(&mut self, u: i64, v: i64) {
        let p = if u == self.root {
            self.root = v;
            return;
        } else {
            self.find_parent_id(u)
        };
        if self.nodes[p as usize].left == u {
            self.nodes[p as usize].left = v;
        } else {
            self.nodes[p as usize].right = v;
        }
    }

    fn fixup_after_delete(
        &mut self,
        mut x: i64,
        mut px: i64,
        mut x_is_left: bool,
    ) -> Result<(), String> {
        loop {
            if x != NIL && self.nodes[x as usize].color.is_red() {
                self.nodes[x as usize].color = Color::B;
                break;
            }
            if x == self.root {
                break;
            }

            let par = if px != NIL {
                px
            } else {
                self.parent_of(x)?
            };
            let is_left = if px != NIL {
                x_is_left
            } else {
                par != NIL && self.nodes[par as usize].left == x
            };
            px = NIL;

            if par == NIL {
                break;
            }

            let w = if is_left {
                self.nodes[par as usize].right
            } else {
                self.nodes[par as usize].left
            };

            if w != NIL && self.nodes[w as usize].color.is_red() {
                self.nodes[w as usize].color = Color::B;
                self.nodes[par as usize].color = Color::R;
                if is_left {
                    self.rotate_left(par);
                } else {
                    self.rotate_right(par);
                }
                px = par;
                x_is_left = is_left;
                continue;
            }

            let w_left = if w != NIL {
                self.nodes[w as usize].left
            } else {
                NIL
            };
            let w_right = if w != NIL {
                self.nodes[w as usize].right
            } else {
                NIL
            };
            let w_left_black = w_left == NIL || self.nodes[w_left as usize].color.is_black();
            let w_right_black = w_right == NIL || self.nodes[w_right as usize].color.is_black();

            if w_left_black && w_right_black {
                if w != NIL {
                    self.nodes[w as usize].color = Color::R;
                }
                x = par;
                continue;
            }

            if is_left {
                if w_left != NIL && self.nodes[w_left as usize].color.is_red() {
                    self.nodes[w as usize].color = self.nodes[par as usize].color;
                    self.nodes[par as usize].color = Color::B;
                    self.nodes[w_right as usize].color = Color::B;
                    self.rotate_left(par);
                    break;
                } else {
                    if w_left != NIL {
                        self.nodes[w_left as usize].color = Color::B;
                    }
                    if w != NIL {
                        self.nodes[w as usize].color = Color::R;
                    }
                    self.rotate_right(w);
                    let new_w = self.nodes[par as usize].right;
                    let new_w_right = self.nodes[new_w as usize].right;
                    self.nodes[new_w as usize].color = self.nodes[par as usize].color;
                    self.nodes[par as usize].color = Color::B;
                    if new_w_right != NIL {
                        self.nodes[new_w_right as usize].color = Color::B;
                    }
                    self.rotate_left(par);
                    break;
                }
            } else {
                if w_right != NIL && self.nodes[w_right as usize].color.is_red() {
                    self.nodes[w as usize].color = self.nodes[par as usize].color;
                    self.nodes[par as usize].color = Color::B;
                    self.nodes[w_left as usize].color = Color::B;
                    self.rotate_right(par);
                    break;
                } else {
                    if w_right != NIL {
                        self.nodes[w_right as usize].color = Color::B;
                    }
                    if w != NIL {
                        self.nodes[w as usize].color = Color::R;
                    }
                    self.rotate_left(w);
                    let new_w = self.nodes[par as usize].left;
                    let new_w_left = self.nodes[new_w as usize].left;
                    self.nodes[new_w as usize].color = self.nodes[par as usize].color;
                    self.nodes[par as usize].color = Color::B;
                    if new_w_left != NIL {
                        self.nodes[new_w_left as usize].color = Color::B;
                    }
                    self.rotate_right(par);
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn delete(&mut self, key: i64) -> Result<(), String> {
        if self.root == NIL {
            return Ok(());
        }

        let z = match self.find_node(key) {
            Some(id) => id,
            None => return Ok(()),
        };

        let has_two_children =
            self.nodes[z as usize].left != NIL && self.nodes[z as usize].right != NIL;

        let y = if has_two_children {
            match self.successor(z) {
                Some(s) => s,
                None => {
                    return Err(format!("successor not found for node {z}"));
                }
            }
        } else {
            z
        };

        let x = if self.nodes[y as usize].left != NIL {
            self.nodes[y as usize].left
        } else {
            self.nodes[y as usize].right
        };

        if has_two_children {
            self.nodes[z as usize].key = self.nodes[y as usize].key;
        }

        let y_old_parent = if y == self.root {
            NIL
        } else {
            self.find_parent_id(y)
        };
        let y_is_left =
            y_old_parent != NIL && self.nodes[y_old_parent as usize].left == y;
        let y_color = self.nodes[y as usize].color;

        self.transplant(y, x);

        self.nodes[y as usize].key = 0;

        if y == self.root {
            self.root = x;
        }

        if y_color.is_black() {
            let (fx, fpx, f_is_left) = if x == NIL {
                (NIL, y_old_parent, y_is_left)
            } else {
                (x, NIL, false)
            };
            self.fixup_after_delete(fx, fpx, f_is_left)?;
        }

        if self.root != NIL {
            self.nodes[self.root as usize].color = Color::B;
        }
        self.recompute_black_heights()?;
        Ok(())
    }
}

#[cfg(not(test))]
fn main() {
    eprintln!("Run MBT verification via: cargo test --example rb_tree");
}

#[allow(dead_code)]
const MAX_NODES: i64 = 4;

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use serde::{Deserialize, Serialize};
    use tla_connect as T;

    use super::{MAX_NODES, RBTree};
    use apalache_learn::model_check::ApalacheMBT;

    #[derive(Serialize)]
    struct RecordedNode {
        key: i64,
        color: String,
        left: i64,
        right: i64,
        bh: i64,
    }

    #[derive(Serialize)]
    struct RecordedState {
        nodes: Vec<RecordedNode>,
        root: i64,
    }

    impl RecordedState {
        fn from_driver(driver: &RBTDriver) -> Self {
            let sorted = driver.tree.nodes_sorted();
            let mut nodes = Vec::with_capacity((MAX_NODES + 1) as usize);
            for id in 0..=MAX_NODES {
                let (_, key, ref color, left, right, bh) = sorted[id as usize];
                nodes.push(RecordedNode {
                    key,
                    color: color.clone(),
                    left,
                    right,
                    bh,
                });
            }
            RecordedState {
                nodes,
                root: driver.tree.root(),
            }
        }
    }

    #[derive(Debug, PartialEq, Eq, Deserialize)]
    struct RBTState {
        nodes: Vec<(i64, i64, String, i64, i64, i64)>,
        root: i64,
    }

    impl T::State for RBTState {
        fn from_spec(value: &itf::Value) -> Result<Self, T::DriverError> {
            let rec = expect_record(value)?;
            let nodes = extract_nodes(extract_field(rec, "nodes")?)?;
            let root = extract_int(rec, "root")?;
            Ok(RBTState { nodes, root })
        }
    }

    impl T::ExtractState<RBTDriver> for RBTState {
        fn from_driver(driver: &RBTDriver) -> Result<Self, T::DriverError> {
            Ok(RBTState {
                nodes: driver.tree.nodes_sorted(),
                root: driver.tree.root(),
            })
        }
    }

    struct RBTDriver {
        tree: RBTree,
        prev_tree_keys: Vec<i64>,
        emitter: Option<T::StateEmitter>,
    }

    impl RBTDriver {
        fn default() -> Self {
            Self {
                tree: RBTree::new(MAX_NODES),
                prev_tree_keys: Vec::new(),
                emitter: None,
            }
        }

        fn with_emitter(
            emitter_pool: &Rc<RefCell<Option<T::StateEmitter>>>,
        ) -> Self {
            let emitter = emitter_pool.borrow_mut().take();
            Self {
                tree: RBTree::new(MAX_NODES),
                prev_tree_keys: Vec::new(),
                emitter,
            }
        }

        fn emit_state(&mut self, action: &str) -> Result<(), T::DriverError> {
            if self.emitter.is_some() {
                let state = RecordedState::from_driver(self);
                if let Some(ref mut emitter) = self.emitter {
                    emitter.emit(action, &state).map_err(|e| {
                        T::DriverError::ActionFailed {
                            action: action.to_string(),
                            reason: e.to_string(),
                        }
                    })?;
                }
            }
            Ok(())
        }

        #[allow(dead_code)]
        fn finish(mut self) -> Option<usize> {
            self.emitter.take().and_then(|e| e.finish().ok())
        }
    }

    impl T::Driver for RBTDriver {
        type State = RBTState;

        fn step(&mut self, step: &T::Step) -> Result<(), T::DriverError> {
            match step.action_taken.as_str() {
                "init" => {
                    self.tree = RBTree::new(MAX_NODES);
                    self.prev_tree_keys.clear();
                    self.emit_state("init")?;
                    Ok(())
                }
                "insert" | "Insert" => {
                    let rec = expect_record(&step.state)?;
                    let node_records = extract_nodes(extract_field(rec, "nodes")?)?;

                    let mut cur_keys: Vec<i64> = node_records
                        .iter()
                        .filter(|(id, key, _, _, _, _)| *id != 0 && *key != 0)
                        .map(|(_, key, _, _, _, _)| *key)
                        .collect();
                    cur_keys.sort();
                    cur_keys.dedup();

                    let new_keys: Vec<i64> = cur_keys
                        .iter()
                        .filter(|k| !self.prev_tree_keys.contains(k))
                        .copied()
                        .collect();

                    for key in &new_keys {
                        self.tree.insert(*key).map_err(|e| {
                            T::DriverError::ActionFailed {
                                action: step.action_taken.clone(),
                                reason: e,
                            }
                        })?;
                    }

                    self.prev_tree_keys = cur_keys;

                    self.emit_state("insert")?;

                    Ok(())
                }
                "delete" | "Delete" => {
                    let rec = expect_record(&step.state)?;
                    let node_records = extract_nodes(extract_field(rec, "nodes")?)?;

                    let mut cur_keys: Vec<i64> = node_records
                        .iter()
                        .filter(|(id, key, _, _, _, _)| *id != 0 && *key != 0)
                        .map(|(_, key, _, _, _, _)| *key)
                        .collect();
                    cur_keys.sort();
                    cur_keys.dedup();

                    let removed_keys: Vec<i64> = self
                        .prev_tree_keys
                        .iter()
                        .filter(|k| !cur_keys.contains(k))
                        .copied()
                        .collect();

                    for key in &removed_keys {
                        self.tree.delete(*key).map_err(|e| {
                            T::DriverError::ActionFailed {
                                action: step.action_taken.clone(),
                                reason: e,
                            }
                        })?;
                    }

                    self.prev_tree_keys = cur_keys;

                    self.emit_state("delete")?;

                    Ok(())
                }
                other => Err(T::DriverError::UnknownAction(other.to_string())),
            }
        }
    }

    fn state_err(msg: impl Into<String>) -> T::DriverError {
        T::DriverError::StateExtraction(msg.into())
    }

    fn expect_record(v: &itf::Value) -> Result<&itf::value::Record, T::DriverError> {
        match v {
            itf::Value::Record(r) => Ok(r),
            other => Err(state_err(format!("expected Record, got {other:?}"))),
        }
    }

    fn extract_field<'a>(
        rec: &'a itf::value::Record,
        field: &str,
    ) -> Result<&'a itf::Value, T::DriverError> {
        rec.get(field)
            .ok_or_else(|| state_err(format!("missing field {field}")))
    }

    fn extract_int(rec: &itf::value::Record, field: &str) -> Result<i64, T::DriverError> {
        let v = extract_field(rec, field)?;
        match v {
            itf::Value::BigInt(n) => n
                .to_string()
                .parse()
                .map_err(|e| state_err(format!("{field}: {e}"))),
            itf::Value::Number(n) => Ok(*n),
            other => Err(state_err(format!("{field}: expected int, got {other:?}"))),
        }
    }

    fn to_i64(v: &itf::Value) -> Result<i64, T::DriverError> {
        match v {
            itf::Value::BigInt(n) => n
                .to_string()
                .parse()
                .map_err(|e| state_err(format!("BigInt: {e}"))),
            itf::Value::Number(n) => Ok(*n),
            other => Err(state_err(format!("expected int, got {other:?}"))),
        }
    }

    fn extract_color(v: &itf::Value) -> Result<String, T::DriverError> {
        match v {
            itf::Value::String(s) => Ok(s.clone()),
            other => Err(state_err(format!("expected String color, got {other:?}"))),
        }
    }

    fn extract_nodes(
        v: &itf::Value,
    ) -> Result<Vec<(i64, i64, String, i64, i64, i64)>, T::DriverError> {
        match v {
            itf::Value::Map(map) => {
                let mut result = Vec::new();
                for (key, val) in map.iter() {
                    let id = to_i64(key)?;
                    let rec = expect_record(val)?;
                    let node_key = extract_int(rec, "key")?;
                    let color = extract_color(extract_field(rec, "color")?)?;
                    let left = extract_int(rec, "left")?;
                    let right = extract_int(rec, "right")?;
                    let bh = extract_int(rec, "bh")?;
                    result.push((id, node_key, color, left, right, bh));
                }
                result.sort_by_key(|(id, _, _, _, _, _)| *id);
                Ok(result)
            }
            other => Err(state_err(format!("expected Map for nodes, got {other:?}"))),
        }
    }

    #[test]
    fn mbt_verify() -> Result<(), T::Error> {
        let mbt = ApalacheMBT::new("examples/RB-Tree/RBT.tla")
            .max_length(4)
            .invariant("TraceComplete")
            .view("TreeView")
            .mode(tla_connect::ApalacheMode::Check);

        mbt.run(RBTDriver::default)
    }

    #[test]
    fn post_hoc_validate() -> Result<(), Box<dyn std::error::Error>> {
        let tmp_dir = tempfile::tempdir()?;
        let trace_path = tmp_dir.path().join("trace.ndjson");

        let emitter = T::StateEmitter::new(&trace_path)?;
        let emitter_pool = Rc::new(RefCell::new(Some(emitter)));

        let mbt = ApalacheMBT::new("examples/RB-Tree/RBT.tla")
            .max_length(4)
            .max_traces(1)
            .invariant("TraceComplete")
            .view("TreeView")
            .mode(tla_connect::ApalacheMode::Check);

        {
            let pool_ref = Rc::clone(&emitter_pool);
            mbt.run(move || RBTDriver::with_emitter(&pool_ref))?;
        }

        drop(emitter_pool);

        let config = T::TraceValidatorConfig::builder()
            .trace_spec("examples/RB-Tree/RBT_Trace.tla")
            .build()?;

        let result = T::validate_trace(&config, &trace_path)?;

        match result {
            T::TraceResult::Valid => {
                println!("Post-hoc validation: trace is valid");
                Ok(())
            }
            T::TraceResult::Invalid { reason } => {
                Err(format!("Post-hoc validation failed: {reason}").into())
            }
            _ => Err("Unexpected trace validation result".into()),
        }
    }
}
