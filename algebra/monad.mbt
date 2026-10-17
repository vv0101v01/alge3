///|
/// Terms of the free monad on a graded signature:
/// - `Var i` is a variable (the unit of the monad),
/// - `Lit n` is a constant,
/// - `Node op args` is an operation with a list of subterms.
///
/// `subst` is the Kleisli composition / monad multiplication.  The three
/// substitution lemmas below are exactly the three monad laws.
pub enum Term {
  Var(Int32)
  Lit(Int32)
  Node(Int32, Array[Term])
} derive(Debug, Eq)

///|
pub fn Term::size(self : Term) -> Int32 {
  match self {
    Var(_) => 1
    Lit(_) => 1
    Node(_, args) => {
      let mut s = 1
      for a in args {
        s = s + a.size()
      }
      s
    }
  }
}

///|
/// Substitute terms for variables.  Variables outside the environment are
/// kept as variables (open terms are allowed).
pub fn Term::subst(self : Term, env : Array[Term]) -> Term {
  match self {
    Var(i) => if i >= 0 && i < env.length() { env[i] } else { self }
    Lit(n) => Lit(n)
    Node(op, args) => {
      let out : Array[Term] = []
      for a in args {
        out.push(a.subst(env))
      }
      Node(op, out)
    }
  }
}

///|
/// Functorial action on variables (the functor underlying the monad).
pub fn Term::map_vars(self : Term, f : (Int32) -> Int32) -> Term {
  match self {
    Var(i) => Var(f(i))
    Lit(n) => Lit(n)
    Node(op, args) => {
      let out : Array[Term] = []
      for a in args {
        out.push(a.map_vars(f))
      }
      Node(op, out)
    }
  }
}

///|
/// Monad unit `pure : X -> T X`.
pub fn pure(x : Int32) -> Term {
  Var(x)
}

///|
/// Monad multiplication `join : T(T X) -> T X` — substitution of the identity
/// environment, i.e. deletion of one layer of `Node`-wrapping of variables.
/// Here `T` is a free term monad; `join` is literally `subst` with `Var`.
pub fn join(t : Term) -> Term {
  let env : Array[Term] = []
  t.subst(env)
}

///|
/// A finite algebra for the signature: `ops[op]` is the operation table as a
/// closure on a carrier represented by `Int`.
pub struct Algebra {
  carrier_size : Int32
  ops : Array[(Array[Int32]) -> Int32]
}

///|
pub fn Algebra::new(
  carrier_size : Int32,
  ops : Array[(Array[Int32]) -> Int32],
) -> Algebra {
  Algebra::{ carrier_size, ops, }
}

///|
/// The unique homomorphism from the free term algebra to `alg`
/// (the Eilenberg–Moore fold).  Existence and uniqueness on closed terms is
/// the universal property of the free monad.
pub fn fold(alg : Algebra, t : Term) -> Int32 {
  match t {
    Var(i) => i
    Lit(n) => n
    Node(op, args) => {
      let vals : Array[Int32] = []
      for a in args {
        vals.push(fold(alg, a))
      }
      alg.ops[op](vals)
    }
  }
}

///|
/// Constant folding: a term homomorphism that replaces every operation whose
/// arguments are all literals by its value.  It is a retraction onto the
/// normal forms and preserves `fold`.
pub fn optimize(alg : Algebra, t : Term) -> Term {
  match t {
    Var(_) => t
    Lit(_) => t
    Node(op, args) => {
      let new_args : Array[Term] = []
      let mut all_lit = true
      let vals : Array[Int32] = []
      for a in args {
        let b = optimize(alg, a)
        match b {
          Lit(n) => vals.push(n)
          _ => all_lit = false
        }
        new_args.push(b)
      }
      if all_lit {
        Lit(alg.ops[op](vals))
      } else {
        Node(op, new_args)
      }
    }
  }
}

///|
/// Distributive law `List ∘ Option -> Option ∘ List` (matrix transposition).
/// This is the standard distributive law between the free-monoid monad and
/// the maybe monad; the hexagon axioms are tested in the test file.
pub fn dist_list_option(xs : Array[Int32?]) -> Array[Int32]? {
  let out : Array[Int32] = []
  let mut failed = false
  for x in xs {
    match x {
      None => failed = true
      Some(v) => out.push(v)
    }
  }
  if failed {
    None
  } else {
    Some(out)
  }
}

///|
/// Count the number of substitution steps in a naive tree substitution;
/// used for the cost table in the paper.  `O(size · |env|)` worst case.
pub fn subst_cost(t : Term, env : Array[Term]) -> Int32 {
  match t {
    Var(i) => if i >= 0 && i < env.length() { env[i].size() } else { 1 }
    Lit(_) => 1
    Node(_, args) => {
      let mut s = 1
      for a in args {
        s = s + subst_cost(a, env)
      }
      s
    }
  }
}
