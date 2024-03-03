import gleam/io
import gleam/int
import gleam/list
import gleam/bool
import gleam/pair
import gleam/dict.{type Dict}
import gleam/result.{try}
import gleam/option.{type Option, None, Some}

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

/// The AST for the hypothetical language. Type annotations are optional, and any
/// missing annotations can be filled in by the `infer` function.
type Expression {
  // A lambda expression, capable of multiple parameters
  ELambda(
    parameters: List(Parameter),
    return_type: Option(Type),
    body: Expression,
  )
  // A function application
  EApply(function: Expression, arguments: List(Expression))
  // A let expression with a body in which the new binding can be used
  ELet(
    name: String,
    type_annotation: Option(Type),
    value: Expression,
    body: Expression,
  )
  // A variable usage
  EVariable(name: String)
  // Value literals
  EInt(value: Int)
  EString(value: String)
  EArray(item_type: Option(Type), items: List(Expression))
}

/// A parameter has a name and an optional type annotation.
type Parameter {
  Parameter(name: String, type_annotation: Option(Type))
}

type Environment =
  Dict(String, Type)

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
  ELet(
    name: "add",
    type_annotation: None,
    value: ELambda(
      parameters: [Parameter("a", None), Parameter("b", None)],
      return_type: None,
      body: EApply(EVariable("+"), [EVariable("a"), EVariable("b")]),
    ),
    body: EApply(EVariable("add"), [EInt(1), EInt(2)]),
  )
  |> infer_expression(initial_environment())
  |> io.debug
  Nil
}

/// Takes an expression and returns the same expression with type annotations
/// inferred and filled in, or an error if type checking failed.
fn infer_expression(
  expression: Expression,
  environment: Environment,
) -> Result(Expression, TypeError) {
  let initial_ctx = Ctx(substitution: dict.new(), type_constraints: [])
  let #(fresh_var, ctx) = fresh_type_variable(initial_ctx)

  // 1. Infer the type of the expression without expecting it to be a certain
  // type by passing a fresh type variable.
  use #(inferred, ctx) <- try(infer(expression, fresh_var, environment, ctx))
  // 2. Solve the generated constraints
  use ctx <- try(solve_constraints(ctx))
  // 3. Replace type variables in the inferred expression with their substitutions
  let result = substitute_expression(inferred, ctx)
  Ok(result)
}

fn initial_environment() -> Dict(String, Type) {
  // Operators in this case are functions. It wouldn't be very difficult to add
  // operators to the Expression type itself, but since the article doesn't I'll
  // hold off for now to keep things simple.
  ["+", "-", "*", "/"]
  |> list.map(fn(op) {
    #(
      op,
      TConstructor("Function2", [
        TConstructor("Int", []),
        TConstructor("Int", []),
        TConstructor("Int", []),
      ]),
    )
  })
  |> dict.from_list
}

// ---- TYPE INFERENCE ---------------------------------------------------------

/// Infer the type of an expression, filling in any missing type annotations with
/// fresh type variables, and adding constraints to things we know should be certain
/// types. The expected type of the expression must be passed to the function,
/// but a fresh type variable can be passed instead to infer without checking.
///
fn infer(
  expression: Expression,
  expected_type: Type,
  environment: Environment,
  ctx: Ctx,
) -> Result(#(Expression, Ctx), TypeError) {
  case expression {
    ELambda(parameters, return_type, body) -> {
      let #(new_return_type, ctx) = type_or_fresh_variable(return_type, ctx)
      let #(new_parameter_types, ctx) =
        map_fold(parameters, ctx, fn(ctx, p) {
          type_or_fresh_variable(p.type_annotation, ctx)
        })
      // Update the parameters to include the new types
      let new_parameters =
        list.map2(parameters, new_parameter_types, fn(p, t) {
          Parameter(..p, type_annotation: Some(t))
        })
      // Add the parameters to the environment
      let new_environment =
        list.fold(new_parameters, environment, fn(env, p) {
          let assert Parameter(name, Some(t)) = p
          dict.insert(env, name, t)
        })
      // Infer the type of the body, expecting it to be the return type (which
      // could be a fresh type variable if an annotation wasn't given)
      use #(new_body, ctx) <- try(infer(
        body,
        new_return_type,
        new_environment,
        ctx,
      ))

      let constructor_name =
        "Function" <> int.to_string(list.length(parameters))

      let ctx =
        push_constraint(
          ctx,
          CEquality(
            expected_type,
            TConstructor(
              constructor_name,
              list.reverse([new_return_type, ..new_parameter_types]),
            ),
          ),
        )

      Ok(#(ELambda(new_parameters, Some(new_return_type), new_body), ctx))
    }

    EApply(function, arguments) -> {
      // Create a fresh type variable for each of the arguments
      let #(argument_types, ctx) =
        map_fold(arguments, ctx, fn(ctx, _) { fresh_type_variable(ctx) })
      // Create a function type based on the arguments and expected return type
      let constructor_name = "Function" <> int.to_string(list.length(arguments))
      let function_type =
        TConstructor(
          constructor_name,
          list.reverse([expected_type, ..argument_types]),
        )
      // Infer the type of function, expecting it to be `function_type`.
      use #(new_function, ctx) <- try(infer(
        function,
        function_type,
        environment,
        ctx,
      ))
      // Infer the missing types of the arguments
      use #(new_arguments, ctx) <- try(
        list.zip(arguments, argument_types)
        |> try_map_fold(ctx, fn(ctx, pair) {
          infer(pair.0, pair.1, environment, ctx)
        }),
      )

      Ok(#(EApply(new_function, new_arguments), ctx))
    }

    EVariable(name) -> {
      case dict.get(environment, name) {
        Ok(t) -> {
          // Constrain the variable type to be the expected type
          let ctx = push_constraint(ctx, CEquality(expected_type, t))
          // Simply return the original expression. There are no type annotations
          // to fill in!
          Ok(#(expression, ctx))
        }
        Error(_) -> Error(TypeError("Variable not in scope: " <> name))
      }
    }

    ELet(name, type_annotation, value, body) -> {
      let #(new_type_annotation, ctx) =
        type_or_fresh_variable(type_annotation, ctx)
      use #(new_value, ctx) <- try(infer(
        value,
        new_type_annotation,
        environment,
        ctx,
      ))
      // Add the variable to the environment so it can be referenced in the body
      let new_environment = dict.insert(environment, name, new_type_annotation)
      use #(new_body, ctx) <- try(infer(
        body,
        expected_type,
        new_environment,
        ctx,
      ))

      Ok(#(ELet(name, Some(new_type_annotation), new_value, new_body), ctx))
    }

    // These literals are easy—we just have to constrain the expected type. There
    // aren't any annotations to fill in.
    EInt(_) -> {
      let ctx =
        push_constraint(ctx, CEquality(expected_type, TConstructor("Int", [])))

      Ok(#(expression, ctx))
    }

    EString(_) -> {
      let ctx =
        push_constraint(
          ctx,
          CEquality(expected_type, TConstructor("String", [])),
        )

      Ok(#(expression, ctx))
    }

    // Array literals are slightly more complex.
    EArray(item_type, items) -> {
      let #(new_item_type, ctx) = type_or_fresh_variable(item_type, ctx)
      // Infer the types of the items, expecting them to be `new_item_type`.
      use #(new_items, ctx) <- try(
        try_map_fold(items, ctx, fn(ctx, item) {
          infer(item, new_item_type, environment, ctx)
        }),
      )
      let ctx =
        push_constraint(
          ctx,
          CEquality(expected_type, TConstructor("Array", [new_item_type])),
        )

      Ok(#(EArray(Some(new_item_type), new_items), ctx))
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

/// Return a fresh type variable if the optional type isn't provided.
///
fn type_or_fresh_variable(annotation: Option(Type), ctx: Ctx) -> #(Type, Ctx) {
  case annotation {
    Some(a) -> #(a, ctx)
    None -> fresh_type_variable(ctx)
  }
}

/// Add a constraint to the type_constraints list.
///
fn push_constraint(ctx: Ctx, constraint: Constraint) -> Ctx {
  Ctx(..ctx, type_constraints: [constraint, ..ctx.type_constraints])
}

// TODO: this function could be easily modified to return multiple type errors
// instead of just the first one.
//
/// "Solve" constraints by going through them and making sure they hold true, then
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

/// Recursively replace solved type variables in an expression with their
/// substitutions.
///
fn substitute_expression(expression: Expression, ctx: Ctx) -> Expression {
  case expression {
    ELambda(parameters, return_type, body) -> {
      let new_return_type = option.map(return_type, substitute(_, ctx))
      let new_parameters =
        list.map(parameters, fn(p) {
          let assert Parameter(name, Some(t)) = p
          Parameter(name, Some(substitute(t, ctx)))
        })
      let new_body = substitute_expression(body, ctx)
      ELambda(new_parameters, new_return_type, new_body)
    }

    EApply(function, arguments) -> {
      let new_function = substitute_expression(function, ctx)
      let new_arguments = list.map(arguments, substitute_expression(_, ctx))
      EApply(new_function, new_arguments)
    }

    EVariable(_) | EInt(_) | EString(_) -> expression

    ELet(name, type_annotation, value, body) -> {
      let new_type_annotation = option.map(type_annotation, substitute(_, ctx))
      let new_value = substitute_expression(value, ctx)
      let new_body = substitute_expression(body, ctx)
      ELet(name, new_type_annotation, new_value, new_body)
    }

    EArray(item_type, items) -> {
      let new_item_type = option.map(item_type, substitute(_, ctx))
      let new_items = list.map(items, substitute_expression(_, ctx))
      EArray(new_item_type, new_items)
    }
  }
}

// ---- UTILS ------------------------------------------------------------------

/// Same as `list.map_fold` but with the return tuples swapped. This function is
/// useful because other functions (such as `fresh_type_variable`) return
/// `#(a, Ctx)` instead of `#(Ctx, a)` and `Ctx` is being folded.
///
fn map_fold(list: List(a), acc: b, fun: fn(b, a) -> #(c, b)) -> #(List(c), b) {
  list.map_fold(list, acc, fn(b, a) {
    fun(b, a)
    |> pair.swap
  })
  |> pair.swap
}

/// A combination of `list.try_fold` and `map_fold`.
///
fn try_map_fold(
  list: List(a),
  folding: b,
  fun: fn(b, a) -> Result(#(c, b), d),
) -> Result(#(List(c), b), d) {
  list.try_fold(list, #([], folding), fn(state, curr) {
    let #(acc, folding) = state
    use #(result, folding) <- try(fun(folding, curr))
    Ok(#([result, ..acc], folding))
  })
  |> result.map(pair.map_first(_, list.reverse))
}
