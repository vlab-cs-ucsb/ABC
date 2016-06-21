/*
 * ArithmeticFormulaTest.cpp
 *
 *  Created on: Oct 21, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ArithmeticFormulaTest.h"

namespace Vlab {
namespace Theory {
namespace Test {

using namespace ::testing;

void ArithmeticFormulaTest::SetUp() {
  coefficients = {1,2,3};
  coeff_index_map = {{"x", 0}, {"y", 1}, {"z", 2}};
}

void ArithmeticFormulaTest::TearDown() {
}

TEST_F(ArithmeticFormulaTest, EmptyConstructor) {
  ArithmeticFormula formula;
  EXPECT_EQ(0, formula.get_constant());
  EXPECT_TRUE(ArithmeticFormula::Type::NONE == formula.get_type());
}

TEST_F(ArithmeticFormulaTest, ConstructorWithArgs) {
  ArithmeticFormula formula(coeff_index_map, coefficients);
  EXPECT_EQ(0, formula.get_constant());
  EXPECT_TRUE(ArithmeticFormula::Type::NONE == formula.get_type());
  EXPECT_THAT(formula.get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_THAT(formula.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
}

TEST_F(ArithmeticFormulaTest, CopyConstructor) {
  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  formula_1.set_type(ArithmeticFormula::Type::LT);
  formula_1.set_constant(3);

  ArithmeticFormula formula_2(formula_1);
  EXPECT_EQ(formula_1.get_constant(), formula_2.get_constant());
  EXPECT_EQ(formula_1.get_type(), formula_2.get_type());

  EXPECT_THAT(formula_2.get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_THAT(formula_2.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
}

TEST_F(ArithmeticFormulaTest, Str) {
  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  formula_1.set_type(ArithmeticFormula::Type::LT);
  formula_1.set_constant(3);

  EXPECT_THAT(formula_1.str(), StrEq("x + 2y + 3z + 3 < 0"));

  formula_1.set_variable_coefficient("x", -1);
  formula_1.set_variable_coefficient("y", -2);
  formula_1.set_constant(0);
  formula_1.set_type(ArithmeticFormula::Type::GE);

  EXPECT_THAT(formula_1.str(), StrEq("-x - 2y + 3z >= 0"));

  formula_1.reset_coefficients();
  formula_1.set_type(ArithmeticFormula::Type::INTERSECT);

  EXPECT_THAT(formula_1.str(), StrEq("x, y, z &"));

  formula_1.set_type(ArithmeticFormula::Type::UNION);

  EXPECT_THAT(formula_1.str(), StrEq("x, y, z |"));
}

TEST_F(ArithmeticFormulaTest, GetVariableCoefficient) {
  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  formula_1.set_type(ArithmeticFormula::Type::LT);
  formula_1.set_constant(3);

  EXPECT_EQ(3, formula_1.get_variable_coefficient("z"));
  EXPECT_EQ(0, formula_1.get_variable_coefficient("a"));
}

TEST_F(ArithmeticFormulaTest, SetVariableCoefficient) {
  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  formula_1.set_type(ArithmeticFormula::Type::LT);
  formula_1.set_constant(3);

  formula_1.set_variable_coefficient("x", -1);
  EXPECT_EQ(-1, formula_1.get_variable_coefficient("x"));
  EXPECT_EQ(0, formula_1.get_variable_coefficient("a"));
  formula_1.set_variable_coefficient("a", 2);
  EXPECT_EQ(2, formula_1.get_variable_coefficient("a"));
}

TEST_F(ArithmeticFormulaTest, IsConstant) {
  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  ArithmeticFormula formula_2;

  EXPECT_FALSE(formula_1.is_constant());
  EXPECT_TRUE(formula_2.is_constant());
}

TEST_F(ArithmeticFormulaTest, IsVariableOrderingSame) {
  std::map<std::string ,int> eq_1 = {{"x", 0}, {"z", 1}, {"y", 2}};
  std::vector<int> coeff = {1, 2, 3};

  ArithmeticFormula formula_1(coeff_index_map, coefficients);
  ArithmeticFormula formula_2(eq_1, coeff);

  EXPECT_TRUE(formula_1.IsVariableOrderingSame(&formula_1));
  EXPECT_FALSE(formula_1.IsVariableOrderingSame(&formula_2));
}

TEST_F(ArithmeticFormulaTest, MergeCoefficients) {
  std::vector<int> coeff_1 = {-1, -2, -3};
  std::vector<int> coeff_3 = {-1, 1, 3, 5, 7};
  std::map<std::string ,int> eq_1 = {{"x", 0}, {"y", 1}, {"z", 2}};
  std::map<std::string ,int> eq_2 = {{"y", 0}, {"z", 1}, {"x", 2}};
  std::map<std::string ,int> eq_3 = {{"a", 0}, {"y", 1}, {"b", 2}, {"z", 3}, {"c", 4}};

  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  ArithmeticFormula formula_1(eq_1, coeff_1);
  ArithmeticFormula formula_2(eq_2, coeff_1);
  ArithmeticFormula formula_3(eq_3, coeff_3);

  formula_0.MergeCoefficients(&formula_1);
  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(1, 2, 3)); // do not update coefficients

  formula_0.MergeCoefficients(&formula_2);
  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("y", 0), Pair("z", 1), Pair("x", 2)));
  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(2, 3, 1)); // do not update coefficients

  formula_0.MergeCoefficients(&formula_3);
  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("a", 0), Pair("y", 1), Pair("b", 2), Pair("z", 3), Pair("c", 4), Pair("x", 5)));
  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(0, 2, 0, 3, 0, 1)); // do not update coefficients
}

TEST_F(ArithmeticFormulaTest, ResetCoefficients) {
  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.reset_coefficients();

  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(0, 0, 0));

  formula_0.reset_coefficients(3);
  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(3, 3, 3));
}

TEST_F(ArithmeticFormulaTest, Substract) {
  std::vector<int> coeff_1 = {-1, -2, -3};
  std::vector<int> coeff_2 = {-1, 1, 3, 5, 7};
  std::map<std::string ,int> eq_1 = {{"x", 0}, {"y", 1}, {"z", 2}};
  std::map<std::string ,int> eq_2 = {{"a", 0}, {"y", 1}, {"b", 2}, {"z", 3}, {"c", 4}};
  ArithmeticFormula_ptr result = nullptr;

  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.set_type(ArithmeticFormula::Type::LT);
  ArithmeticFormula formula_1(eq_1, coeff_1);
  formula_1.set_constant(5);
  ArithmeticFormula formula_2(eq_2, coeff_2);
  formula_2.set_constant(-3);

  result = formula_0.Substract(&formula_1);
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(2, 4, 6));
  EXPECT_EQ(-5, result->get_constant());
  delete result;

  result = formula_0.Substract(&formula_2);
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("a", 0), Pair("y", 1), Pair("b", 2), Pair("z", 3), Pair("c", 4), Pair("x", 5)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 1, -3, -2, -7, 1));
  EXPECT_EQ(3, result->get_constant());
  delete result;
}

TEST_F(ArithmeticFormulaTest, Add) {
  std::vector<int> coeff_1 = {-1, -2, -3};
  std::vector<int> coeff_2 = {-1, 1, 3, 5, 7};
  std::map<std::string ,int> eq_1 = {{"x", 0}, {"y", 1}, {"z", 2}};
  std::map<std::string ,int> eq_2 = {{"a", 0}, {"y", 1}, {"b", 2}, {"z", 3}, {"c", 4}};
  ArithmeticFormula_ptr result = nullptr;

  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.set_type(ArithmeticFormula::Type::LT);
  ArithmeticFormula formula_1(eq_1, coeff_1);
  formula_1.set_constant(5);
  ArithmeticFormula formula_2(eq_2, coeff_2);
  formula_2.set_constant(-3);

  result = formula_0.Add(&formula_1);
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(0, 0, 0));
  EXPECT_EQ(5, result->get_constant());
  delete result;

  result = formula_0.Add(&formula_2);
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("a", 0), Pair("y", 1), Pair("b", 2), Pair("z", 3), Pair("c", 4), Pair("x", 5)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(-1, 3, 3, 8, 7, 1));
  EXPECT_EQ(-3, result->get_constant());
  delete result;
}

TEST_F(ArithmeticFormulaTest, Negate) {
  ArithmeticFormula_ptr result = nullptr;
  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.set_type(ArithmeticFormula::Type::EQ);

  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::NOTEQ, result->get_type());
  delete result;

  formula_0.set_type(ArithmeticFormula::Type::NOTEQ);
  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::EQ, result->get_type());
  delete result;

  formula_0.set_type(ArithmeticFormula::Type::GT);
  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::LE, result->get_type());
  delete result;

  formula_0.set_type(ArithmeticFormula::Type::GE);
  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::LT, result->get_type());
  delete result;

  formula_0.set_type(ArithmeticFormula::Type::LT);
  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::GE, result->get_type());
  delete result;

  formula_0.set_type(ArithmeticFormula::Type::LE);
  result = formula_0.NegateOperation();
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(0, result->get_constant());
  EXPECT_EQ(ArithmeticFormula::Type::GT, result->get_type());
  delete result;
}

TEST_F(ArithmeticFormulaTest, Multiply) {
  ArithmeticFormula_ptr result = nullptr;

  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.set_type(ArithmeticFormula::Type::LT);
  formula_0.set_constant(4);

  result = formula_0.Multiply(-2);
  EXPECT_THAT(result->get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(result->get_coefficients(), ElementsAre(-2, -4, -6));
  EXPECT_EQ(-8, result->get_constant());
  delete result;
}

TEST_F(ArithmeticFormulaTest, Simplify) {
  std::vector<int> coeff_1 = {2, 4, 6};
  std::vector<int> coeff_2 = {2};
  std::map<std::string, int> coeff_index_2 = { {"x", 0} };

  ArithmeticFormula formula_0(coeff_index_map, coeff_1);
  formula_0.set_type(ArithmeticFormula::Type::LT);
  formula_0.set_constant(5);

  ArithmeticFormula formula_1(coeff_index_map, coeff_1);
  formula_1.set_type(ArithmeticFormula::Type::EQ);
  formula_1.set_constant(5);

  ArithmeticFormula formula_2(coeff_index_map, coeff_1);
  formula_2.set_type(ArithmeticFormula::Type::LT);
  formula_2.set_constant(-5);

  ArithmeticFormula formula_3(coeff_index_2, coeff_2);
  formula_3.set_type(ArithmeticFormula::Type::LT);
  formula_3.set_constant(3);

  EXPECT_TRUE(formula_0.Simplify());
  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(2, formula_0.get_constant());

  EXPECT_FALSE(formula_1.Simplify());
  EXPECT_THAT(formula_1.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(formula_1.get_coefficients(), ElementsAre(2, 4, 6));
  EXPECT_EQ(5, formula_1.get_constant());

  EXPECT_TRUE(formula_2.Simplify());
  EXPECT_THAT(formula_2.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
  EXPECT_THAT(formula_2.get_coefficients(), ElementsAre(1, 2, 3));
  EXPECT_EQ(-3, formula_2.get_constant());

  EXPECT_TRUE(formula_3.Simplify());
  EXPECT_THAT(formula_3.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0)));
  EXPECT_THAT(formula_3.get_coefficients(), ElementsAre(1));
  EXPECT_EQ(1, formula_3.get_constant());
}

TEST_F(ArithmeticFormulaTest, CountOnes) {
  ArithmeticFormula formula_0(coeff_index_map, coefficients);
  formula_0.set_type(ArithmeticFormula::Type::LT);
  formula_0.set_constant(5);

  EXPECT_EQ(6, formula_0.CountOnes(15));
  EXPECT_EQ(6, formula_0.CountOnes(7));
  EXPECT_EQ(3, formula_0.CountOnes(3));
  EXPECT_EQ(4, formula_0.CountOnes(5));
}



} /* namespace Test */
} /* namespace Theory */
} /* namespace Vlab */
