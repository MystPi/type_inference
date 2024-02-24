import gleam/io
import gleam/list
import gleam/bool
import gleam/dict.{type Dict}
import gleam/result.{try}

// ---- TYPES ------------------------------------------------------------------

/// A Type can be a type constructor or a type variable.
///
/// - `Int` -> `TConstructor("Int", [])`
/// - `List(Int)` -> `TConstructor("List", [TConstructor("Int", [])])`
/// - `(Int, Int) => Int` -> `TConstructor("Function2", [TConstructor("Int", []), TConstructor("Int", []), TConstructor("Int", [])])`
/// - `$1` -> `TVariable(1)`
type Type {
  /// A constructor has a name and list of type parameters.
  TConstructor(name: String, generics: List(Type))
  /// A type variable is identified by it's index, which is generated when using
  /// the `fresh_type_variable` function.
  TVariable(index: Int)
}

/// The AST for the hypothetical language
type Expression {
  ELambda(arg: String, body: Expression)
  EApply(expression: Expression, arg: Expression)
  EVariable(name: String)
}

/// A constraint is something we know about types and their relationships
type Constraint {
  /// This constraint means the two types must be equal
  CEquality(t1: Type, t2: Type)
}

/// The context holds stuff we've discovered when typchecking.
type Ctx {
  Ctx(substitution: Dict(Int, Type), type_constraints: List(Constraint))
}

type TypeError {
  TypeError(message: String)
}

// ---- TESTING ----------------------------------------------------------------

pub fn main() {
  ELambda("x", EApply(EApply(EVariable("+"), EVariable("x")), EVariable("x")))
  |> infer
  |> io.debug
  Nil
}

fn initial_environment() -> Dict(String, Type) {
  ["+", "-", "*", "/"]
  |> list.map(fn(op) {
    #(
      op,
      TConstructor("Function1", [
        TConstructor("Int", []),
        TConstructor("Function1", [
          TConstructor("Int", []),
          TConstructor("Int", []),
        ]),
      ]),
    )
  })
  |> dict.from_list
}

fn initial_ctx() -> Ctx {
  Ctx(dict.new(), [])
}

fn infer(expression: Expression) -> Result(Type, TypeError) {
  // 1. Infer the type of the expression
  use #(inferred, ctx) <- try(infer_type(
    expression,
    initial_environment(),
    initial_ctx(),
  ))
  // 2. Solve the constraints
  use ctx <- try(solve_constraints(ctx))
  // 3. Replace type variables in the inferred type with their substitutions
  let result = substitute(inferred, ctx)
  Ok(result)
}

// ---- TYPE INFERENCE ---------------------------------------------------------

/// Turn an expression into type variables, adding constraints to things we know
/// must be certain types, and inserting variables and functions into the environment
/// when appropriate.
///
fn infer_type(
  expression: Expression,
  environment: Dict(String, Type),
  ctx: Ctx,
) -> Result(#(Type, Ctx), TypeError) {
  case expression {
    ELambda(name, body) -> {
      let #(arg_type, ctx) = fresh_type_variable(ctx)
      let environment2 = dict.insert(environment, name, arg_type)
      use #(return_type, ctx) <- try(infer_type(body, environment2, ctx))
      Ok(#(TConstructor("Function1", [arg_type, return_type]), ctx))
    }

    EVariable(name) ->
      case dict.get(environment, name) {
        Ok(t) -> Ok(#(t, ctx))
        Error(_) -> Error(TypeError("Variable not defined: " <> name))
      }

    EApply(function, arg) -> {
      use #(function_type, ctx) <- try(infer_type(function, environment, ctx))
      use #(arg_type, ctx) <- try(infer_type(arg, environment, ctx))
      let #(return_type, ctx) = fresh_type_variable(ctx)

      let constraint =
        CEquality(
          function_type,
          TConstructor("Function1", [arg_type, return_type]),
        )
      let ctx = push_constraint(ctx, constraint)

      Ok(#(return_type, ctx))
    }
  }
}

/// Create a "fresh" type variable and add it to the substitution dictionary.
///
fn fresh_type_variable(ctx: Ctx) -> #(Type, Ctx) {
  let index = dict.size(ctx.substitution)
  let result = TVariable(index)
  #(result, insert_substitution(ctx, index, result))
}

/// Add a constraint to the type_constraints list.
///
fn push_constraint(ctx: Ctx, constraint: Constraint) -> Ctx {
  Ctx(..ctx, type_constraints: [constraint, ..ctx.type_constraints])
}

// TODO: this function could be easily modified to return multiple type errors
// instead of just the first one.
//
/// "Solve" constraints by going through them and making sure they are true, then
/// clearing the constraints list.
///
fn solve_constraints(ctx: Ctx) -> Result(Ctx, TypeError) {
  use ctx <- try(
    list.try_fold(ctx.type_constraints, ctx, fn(ctx, constraint) {
      let CEquality(t1, t2) = constraint
      unify(t1, t2, ctx)
    }),
  )
  Ok(Ctx(..ctx, type_constraints: []))
}

/// Check that both types (`t1` and `t2`) are equal, filling in any type variables
/// in the substitution dictionary.
///
fn unify(t1: Type, t2: Type, ctx: Ctx) -> Result(Ctx, TypeError) {
  case t1, t2 {
    // Both types are type constructors...
    TConstructor(name1, generics1), TConstructor(name2, generics2) -> {
      // ...and must have the same name and amount of generics.
      use <- bool.guard(
        when: name1 != name2 || list.length(generics1) != list.length(generics2),
        return: Error(TypeError("Type mismatch: " <> name1 <> " and " <> name2)),
      )
      // Unify the generics from both type constructors
      list.zip(generics1, generics2)
      |> list.try_fold(ctx, fn(ctx, generics) {
        let #(t1, t2) = generics
        unify(t1, t2, ctx)
      })
    }

    // If both types are the same type variable, do nothing
    TVariable(i), TVariable(j) if i == j -> Ok(ctx)

    // If one of the types is a type variable...
    //
    // Does it reference itself in the substitution dictionary?
    //   ↪ no: unify the type variable's substitution with the other type
    //   ↪ yes: Does it occur in the other type?
    //     ↪ yes: return an error
    //     ↪ no: update the substitution dictionary, replacing the type variable's
    //           substitution with the other type
    TVariable(i), _ -> {
      use <- does_ref_self(i, ctx, no: unify(_, t2, ctx))

      case occurs_in(i, t2, ctx) {
        True -> Error(TypeError("Usage of recursive type variable"))
        False -> Ok(insert_substitution(ctx, i, t2))
      }
    }

    // Same thing here, but with the other type
    _, TVariable(i) -> {
      use <- does_ref_self(i, ctx, no: unify(t1, _, ctx))

      case occurs_in(i, t1, ctx) {
        True -> Error(TypeError("Usage of recursive type variable"))
        False -> Ok(insert_substitution(ctx, i, t1))
      }
    }
  }
}

/// Returns True if the type variable (referenced by its `index`) is is used in
/// the type `t`.
///
fn occurs_in(index: Int, t: Type, ctx: Ctx) -> Bool {
  case t {
    TVariable(i) -> {
      use <- does_ref_self(i, ctx, no: occurs_in(index, _, ctx))
      i == index
    }
    TConstructor(_, generics) -> list.any(generics, occurs_in(index, _, ctx))
  }
}

/// Detect if a type variable's substitution references itself. If it does, run
/// the `yes` function, otherwise run the `no` function with the type variable's
/// substitution.
///
fn does_ref_self(
  index: Int,
  ctx: Ctx,
  yes true: fn() -> a,
  no false: fn(Type) -> a,
) -> a {
  let assert Ok(sub) = dict.get(ctx.substitution, index)

  case sub == TVariable(index) {
    True -> true()
    False -> false(sub)
  }
}

/// Update or create a type variable in the substitution dictionary with a type.
///
fn insert_substitution(ctx: Ctx, index: Int, t: Type) -> Ctx {
  Ctx(..ctx, substitution: dict.insert(ctx.substitution, index, t))
}

/// Recursively replace all type variables in the given type with their substitutions.
///
fn substitute(t: Type, ctx: Ctx) -> Type {
  case t {
    TVariable(i) -> {
      // If the type variable references itself, we don't want to run substitute
      // on it again! That would cause an infinite loop
      use <- does_ref_self(i, ctx, no: substitute(_, ctx))
      t
    }

    TConstructor(name, generics) ->
      TConstructor(name, list.map(generics, substitute(_, ctx)))
  }
}
