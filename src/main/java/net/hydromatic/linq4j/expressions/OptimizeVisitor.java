/*
// Licensed to Julian Hyde under one or more contributor license
// agreements. See the NOTICE file distributed with this work for
// additional information regarding copyright ownership.
//
// Julian Hyde licenses this file to you under the Apache License,
// Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at:
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
*/
package net.hydromatic.linq4j.expressions;

import java.util.ArrayList;
import java.util.List;

import static net.hydromatic.linq4j.expressions.ExpressionType.Equal;
import static net.hydromatic.linq4j.expressions.ExpressionType.NotEqual;

/**
 * Visitor that optimizes expressions.
 * <p/>
 * <p>The optimizations are essential, not mere tweaks. Without
 * optimization, expressions such as {@code false == null} will be left in,
 * which are invalid to Janino (because it does not automatically box
 * primitives).</p>
 */
public class OptimizeVisitor extends Visitor {
  public static final ConstantExpression FALSE_EXPR =
      Expressions.constant(false);
  public static final ConstantExpression TRUE_EXPR =
      Expressions.constant(true);
  public static final MemberExpression BOXED_FALSE_EXPR =
      Expressions.field(null, Boolean.class, "FALSE");
  public static final MemberExpression BOXED_TRUE_EXPR =
      Expressions.field(null, Boolean.class, "TRUE");
  public static final Statement EMPTY_STATEMENT = Expressions.statement(null);

  @Override
  public Expression visit(
      TernaryExpression ternary,
      Expression expression0,
      Expression expression1,
      Expression expression2) {
    switch (ternary.getNodeType()) {
    case Conditional:
      Boolean always = always(expression0);
      if (always != null) {
        // true ? y : z  ===  y
        // false ? y : z  === z
        return always
            ? expression1
            : expression2;
      }
      if (expression1.equals(expression2)) {
        // a ? b : b   ===   b
        return expression1;
      }
      // !a ? b : c == a ? c : b
      if (expression0 instanceof UnaryExpression) {
        UnaryExpression una = (UnaryExpression) expression0;
        if (una.getNodeType() == ExpressionType.Not) {
          return Expressions.makeTernary(ternary.getNodeType(),
              una.expression, expression2, expression1);
        }
      }
    }
    return super.visit(ternary, expression0, expression1, expression2);
  }

  @Override
  public Expression visit(
      BinaryExpression binary,
      Expression expression0,
      Expression expression1) {
    //
    Expression result;
    switch (binary.getNodeType()) {
    case Assign:
      if (expression0.equals(expression1)) {
        return expression0.accept(this);
      }
    }
    switch (binary.getNodeType()) {
    case Equal:
    case NotEqual:
      if (expression0.equals(expression1)) {
        return binary.getNodeType() == Equal ? TRUE_EXPR : FALSE_EXPR;
      } else if (expression0 instanceof ConstantExpression && expression1
        instanceof ConstantExpression) {
        ConstantExpression c0 = (ConstantExpression) expression0;
        ConstantExpression c1 = (ConstantExpression) expression1;
        if (c0.value == null && c1.value == null) {
          // Nulls of all types are equal
          return binary.getNodeType() == Equal ? TRUE_EXPR : FALSE_EXPR;
        }
        if (c0.getType() == c1.getType()) {
          return binary.getNodeType() == NotEqual ? TRUE_EXPR : FALSE_EXPR;
        }
      }
      // drop down
    case AndAlso:
    case OrElse:
      result = visit0(binary, expression0, expression1);
      if (result != null) {
        return result;
      }
      result = visit0(binary, expression1, expression0);
      if (result != null) {
        return result;
      }
    }
    return super.visit(binary, expression0, expression1);
  }

  private Expression visit0(
      BinaryExpression binary,
      Expression expression0,
      Expression expression1) {
    Boolean always;
    switch (binary.getNodeType()) {
    case AndAlso:
      always = always(expression0);
      if (always != null) {
        return always
            ? expression1
            : FALSE_EXPR;
      }
      break;
    case OrElse:
      always = always(expression0);
      if (always != null) {
        // true or x  --> true
        // false or x --> x
        return always
            ? TRUE_EXPR
            : expression1;
      }
      break;
    case Equal:
      if (isConstantNull(expression1)
          && Primitive.is(expression0.getType())) {
        return FALSE_EXPR;
      }
      // a == true  -> a
      // a == false -> !a
      always = always(expression0);
      if (always != null) {
        return always ? expression1 : Expressions.not(expression1);
      }
      break;
    case NotEqual:
      if (isConstantNull(expression1)
          && Primitive.is(expression0.getType())) {
        return TRUE_EXPR;
      }
      // a != true  -> !a
      // a != false -> a
      always = always(expression0);
      if (always != null) {
        return always ? Expressions.not(expression1) : expression1;
      }
      break;
    }
    return null;
  }

  @Override
  public Expression visit(UnaryExpression unaryExpression, Expression
      expression) {
    if (unaryExpression.getNodeType() == ExpressionType.Convert) {
      if (expression.getType() == unaryExpression.getType()) {
        return expression;
      }
      if (expression instanceof ConstantExpression) {
        return Expressions.constant(((ConstantExpression) expression).value,
            unaryExpression.getType());
      }
    }
    return super.visit(unaryExpression, expression);
  }

  @Override
  public Statement visit(ConditionalStatement conditionalStatement,
                         List<Node> list) {
    // if (false) { <-- remove branch
    // } if (true) { <-- stop here
    // } else if (...)
    // } else {...}
    boolean optimal = true;
    for (int i = 0; i < list.size() - 1 && optimal; i += 2) {
      Boolean always = always((Expression) list.get(i));
      if (always == null) {
        continue;
      }
      if (i == 0 && always) {
        // when the very first test is always true, just return its statement
        return (Statement) list.get(1);
      }
      optimal = false;
    }
    if (optimal) {
      // Nothing to optimize
      return super.visit(conditionalStatement, list);
    }
    List<Node> newList = new ArrayList<Node>(list.size());
    // Iterate over all the tests, except the latest "else"
    for (int i = 0; i < list.size() - 1; i += 2) {
      Expression test = (Expression) list.get(i);
      Node stmt = list.get(i + 1);
      Boolean always = always(test);
      if (always == null) {
        newList.add(test);
        newList.add(stmt);
        continue;
      }
      if (always) {
        // No need to verify other tests
        newList.add(stmt);
        break;
      }
    }
    // We might have dangling "else", however if we have just single item
    // it means we have if (false) else if(false) else if (true) {...} code.
    // Then we just return statement from true branch
    if (list.size() == 1) {
      return (Statement) list.get(0);
    }
    // Add "else" from original list
    if (newList.size() % 2 == 0 && list.size() % 2 == 1) {
      Node elseBlock = list.get(list.size() - 1);
      if (newList.isEmpty()) {
        return (Statement) elseBlock;
      }
      newList.add(elseBlock);
    }
    if (newList.isEmpty()) {
      return EMPTY_STATEMENT;
    }
    return super.visit(conditionalStatement, newList);
  }

  private boolean isConstantNull(Expression expression) {
    return expression instanceof ConstantExpression
        && ((ConstantExpression) expression).value == null;
  }

  /**
   * Returns whether an expression always evaluates to true or false.
   * Assumes that expression has already been optimized.
   */
  private static Boolean always(Expression x) {
    if (x.equals(FALSE_EXPR) || x.equals(BOXED_FALSE_EXPR)) {
      return Boolean.FALSE;
    }
    if (x.equals(TRUE_EXPR) || x.equals(BOXED_TRUE_EXPR)) {
      return Boolean.TRUE;
    }
    return null;
  }
}
