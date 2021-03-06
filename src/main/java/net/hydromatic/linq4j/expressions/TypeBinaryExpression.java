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

import java.lang.reflect.Type;

/**
 * Represents an operation between an expression and a type.
 */
public class TypeBinaryExpression extends Expression {
  private final Expression expression;
  private final Type type;

  public TypeBinaryExpression(ExpressionType nodeType, Expression expression,
      Type type) {
    super(nodeType, Boolean.TYPE);
    this.expression = expression;
    this.type = type;
  }

  @Override
  public Expression accept(Visitor visitor) {
    Expression expression = this.expression.accept(visitor);
    return visitor.visit(this, expression);
  }

  void accept(ExpressionWriter writer, int lprec, int rprec) {
    if (writer.requireParentheses(this, lprec, rprec)) {
      return;
    }
    expression.accept(writer, lprec, nodeType.lprec);
    writer.append(nodeType.op);
    writer.append(type);
  }
}

// End TypeBinaryExpression.java
