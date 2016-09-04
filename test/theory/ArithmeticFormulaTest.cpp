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

class PublicArithmeticFormula : public ArithmeticFormula {
 public:
  using ArithmeticFormula::type_;
  using ArithmeticFormula::constant_;
  using ArithmeticFormula::variable_coefficient_map_;
};

using namespace ::testing;

void ArithmeticFormulaTest::SetUp() {
  variable_coefficient_map_ = {{"x", 1}, {"y", 2}, {"z", 1}};
}

void ArithmeticFormulaTest::TearDown() {
}

TEST_F(ArithmeticFormulaTest, EmptyConstructor) {
  PublicArithmeticFormula formula;
  EXPECT_EQ(0, formula.constant_);
  EXPECT_TRUE(ArithmeticFormula::Type::NONE == formula.type_);
}

TEST_F(ArithmeticFormulaTest, CopyConstructor) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  PublicArithmeticFormula formula_2(formula_1);
  EXPECT_EQ(formula_1.constant_, formula_2.constant_);
  EXPECT_EQ(formula_1.type_, formula_2.type_);

  EXPECT_THAT(formula_2.variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
}

TEST_F(ArithmeticFormulaTest, Str) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  EXPECT_THAT(formula_1.str(), StrEq(" + x + 2y + z + 3 < 0"));

  formula_1.type_ = ArithmeticFormula::Type::GE;
  formula_1.variable_coefficient_map_["x"] = -1;
  formula_1.variable_coefficient_map_["y"] = -2;
  formula_1.set_variable_coefficient("x", -1);
  formula_1.constant_ = 0;
  EXPECT_THAT(formula_1.str(), StrEq(" - x - 2y + z >= 0"));


  formula_1.type_ = ArithmeticFormula::Type::INTERSECT;
  EXPECT_THAT(formula_1.str(), HasSubstr(" & 0"));

  formula_1.type_ = ArithmeticFormula::Type::UNION;
  EXPECT_THAT(formula_1.str(), HasSubstr(" | 0"));
}

TEST_F(ArithmeticFormulaTest, SetType) {
  PublicArithmeticFormula formula_1;
  formula_1.set_type(ArithmeticFormula::Type::LT);
  EXPECT_EQ(ArithmeticFormula::Type::LT, formula_1.type_);
}

TEST_F(ArithmeticFormulaTest, GetType) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::GE;
  EXPECT_EQ(ArithmeticFormula::Type::GE, formula_1.get_type());
}

TEST_F(ArithmeticFormulaTest, GetNumberOfVariables) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;
  EXPECT_EQ(3, formula_1.get_number_of_variables());
}

TEST_F(ArithmeticFormulaTest, GetVariableCoefficient) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  EXPECT_EQ(2, formula_1.get_variable_coefficient("y"));
  EXPECT_DEATH(formula_1.get_variable_coefficient("a"), "");
}

TEST_F(ArithmeticFormulaTest, SetVariableCoefficient) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  formula_1.set_variable_coefficient("x", -1);
  EXPECT_EQ(-1, formula_1.variable_coefficient_map_["x"]);
  EXPECT_DEATH(formula_1.set_variable_coefficient("a", 2), "");
}

TEST_F(ArithmeticFormulaTest, AddVariable) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  formula_1.add_variable("a", -4);
  EXPECT_THAT(formula_1.variable_coefficient_map_, ElementsAre(Pair("a", -4), Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_DEATH(formula_1.add_variable("x", 2), "");
}

TEST_F(ArithmeticFormulaTest, GetCoefficients) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  EXPECT_THAT(formula_1.get_coefficients(), ElementsAre(1, 2, 1));
}

TEST_F(ArithmeticFormulaTest, GetConstant) {
  PublicArithmeticFormula formula_1;
  formula_1.constant_ = 4;
  EXPECT_EQ(4, formula_1.get_constant());
}

TEST_F(ArithmeticFormulaTest, SetConstant) {
  PublicArithmeticFormula formula_1;
  formula_1.set_constant(-3);
  EXPECT_EQ(-3, formula_1.constant_);
}

TEST_F(ArithmeticFormulaTest, IsConstant) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  EXPECT_FALSE(formula_1.is_constant());
  formula_1.variable_coefficient_map_ = {{"x", 0}, {"y", 0}, {"z", 0}};
  EXPECT_TRUE(formula_1.is_constant());
}

TEST_F(ArithmeticFormulaTest, ResetCoefficients) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  formula_1.reset_coefficients();
  EXPECT_THAT(formula_1.variable_coefficient_map_, ElementsAre(Pair("x", 0), Pair("y", 0), Pair("z", 0)));
  EXPECT_EQ(3, formula_1.constant_);
  formula_1.reset_coefficients(2);
  EXPECT_THAT(formula_1.variable_coefficient_map_, ElementsAre(Pair("x", 2), Pair("y", 2), Pair("z", 2)));
}

TEST_F(ArithmeticFormulaTest, GetVariableIndex) {
  PublicArithmeticFormula formula_1;
  formula_1.type_ = ArithmeticFormula::Type::LT;
  formula_1.variable_coefficient_map_ = variable_coefficient_map_;
  formula_1.constant_ = 3;

  EXPECT_EQ(0, formula_1.get_variable_index("x"));
  EXPECT_EQ(1, formula_1.get_variable_index("y"));
  EXPECT_EQ(2, formula_1.get_variable_index("z"));
  formula_1.variable_coefficient_map_["a"] = 1;
  EXPECT_EQ(0, formula_1.get_variable_index("a"));
  EXPECT_EQ(1, formula_1.get_variable_index("x"));
  EXPECT_EQ(2, formula_1.get_variable_index("y"));
  EXPECT_EQ(3, formula_1.get_variable_index("z"));
}

TEST_F(ArithmeticFormulaTest, Add) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = variable_coefficient_map_;
  formula_0.constant_ = 0;
  PublicArithmeticFormula formula_1;
  formula_1.variable_coefficient_map_ = {{"x", -1}, {"y", -2}, {"z", -3}};
  formula_1.constant_ = 5;
  PublicArithmeticFormula formula_2;
  formula_2.variable_coefficient_map_= {{"a", -1}, {"y", 1}, {"b", 3}, {"z", 5}, {"c", 7}};
  formula_2.constant_ = -3;

  auto result = formula_0.Add(&formula_1);
  PublicArithmeticFormula* presult = static_cast<PublicArithmeticFormula*>(result);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 0), Pair("y", 0), Pair("z", -2)));
  EXPECT_EQ(5, presult->constant_);
  delete result;

  result = formula_0.Add(&formula_2);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("a", -1), Pair("b", 3), Pair("c", 7), Pair("x", 1), Pair("y", 3), Pair("z", 6)));
  EXPECT_EQ(-3, presult->constant_);
  delete result;
}

TEST_F(ArithmeticFormulaTest, Substract) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = variable_coefficient_map_;
  formula_0.constant_ = 0;
  PublicArithmeticFormula formula_1;
  formula_1.variable_coefficient_map_ = {{"x", -1}, {"y", -2}, {"z", -3}};
  formula_1.constant_ = 5;
  PublicArithmeticFormula formula_2;
  formula_2.variable_coefficient_map_= {{"a", -1}, {"y", 1}, {"b", 3}, {"z", 5}, {"c", 7}};
  formula_2.constant_ = -3;

  auto result = formula_0.Subtract(&formula_1);
  PublicArithmeticFormula* presult = static_cast<PublicArithmeticFormula*>(result);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 2), Pair("y", 4), Pair("z", 4)));
  EXPECT_EQ(-5, presult->constant_);
  delete result;

  result = formula_0.Subtract(&formula_2);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("a", 1), Pair("b", -3), Pair("c", -7), Pair("x", 1), Pair("y", 1), Pair("z", -4)));
  EXPECT_EQ(3, presult->constant_);
  delete result;
}

TEST_F(ArithmeticFormulaTest, Multiply) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = variable_coefficient_map_;
  formula_0.constant_ = 5;
  formula_0.type_ = ArithmeticFormula::Type::EQ;

  auto result = formula_0.Multiply(-2);
  PublicArithmeticFormula* presult = static_cast<PublicArithmeticFormula*>(result);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", -2), Pair("y", -4), Pair("z", -2)));
  EXPECT_EQ(-10, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::EQ, presult->type_);
  delete result;
}

TEST_F(ArithmeticFormulaTest, negate) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = variable_coefficient_map_;
  formula_0.constant_ = 5;
  formula_0.type_ = ArithmeticFormula::Type::EQ;

  auto result = formula_0.negate();
  PublicArithmeticFormula* presult = static_cast<PublicArithmeticFormula*>(result);

  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::NOTEQ, presult->type_);
  delete result;

  formula_0.type_ = ArithmeticFormula::Type::NOTEQ;
  result = formula_0.negate();
  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::EQ, presult->type_);
  delete result;

  formula_0.type_ = ArithmeticFormula::Type::GT;
  result = formula_0.negate();
  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::LE, presult->type_);
  delete result;

  formula_0.type_ = ArithmeticFormula::Type::GE;
  result = formula_0.negate();
  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::LT, presult->type_);
  delete result;

  formula_0.type_ = ArithmeticFormula::Type::LT;
  result = formula_0.negate();
  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::GE, presult->type_);
  delete result;

  formula_0.type_ = ArithmeticFormula::Type::LE;
  result = formula_0.negate();
  EXPECT_THAT(presult->variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 1)));
  EXPECT_EQ(5, presult->constant_);
  EXPECT_EQ(ArithmeticFormula::Type::GT, presult->type_);
  delete result;
}

TEST_F(ArithmeticFormulaTest, Simplify) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = {{"x", 2}, {"y", 4}, {"z", 6}};
  formula_0.constant_ = 5;
  formula_0.type_ = ArithmeticFormula::Type::LT;

  EXPECT_TRUE(formula_0.Simplify());
  EXPECT_THAT(formula_0.variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 3)));
  EXPECT_EQ(2, formula_0.constant_);

  PublicArithmeticFormula formula_1;
  formula_1.variable_coefficient_map_ = {{"x", 2}, {"y", 4}, {"z", 6}};
  formula_1.constant_ = 5;
  formula_1.type_ = ArithmeticFormula::Type::EQ;

  EXPECT_FALSE(formula_1.Simplify());
  EXPECT_THAT(formula_1.variable_coefficient_map_, ElementsAre(Pair("x", 2), Pair("y", 4), Pair("z", 6)));
  EXPECT_EQ(5, formula_1.constant_);

  PublicArithmeticFormula formula_2;
  formula_2.variable_coefficient_map_ = {{"x", 2}, {"y", 4}, {"z", 6}};
  formula_2.constant_ = -5;
  formula_2.type_ = ArithmeticFormula::Type::LT;

  EXPECT_TRUE(formula_2.Simplify());
  EXPECT_THAT(formula_2.variable_coefficient_map_, ElementsAre(Pair("x", 1), Pair("y", 2), Pair("z", 3)));
  EXPECT_EQ(-3, formula_2.constant_);

  PublicArithmeticFormula formula_3;
  formula_3.variable_coefficient_map_ = {{"x", 2}};
  formula_3.constant_ = 3;
  formula_3.type_ = ArithmeticFormula::Type::LT;

  EXPECT_TRUE(formula_3.Simplify());
  EXPECT_THAT(formula_3.variable_coefficient_map_, ElementsAre(Pair("x", 1)));
  EXPECT_EQ(1, formula_3.constant_);
}

TEST_F(ArithmeticFormulaTest, CountOnes) {
  PublicArithmeticFormula formula_0;
  formula_0.variable_coefficient_map_ = {{"x", 1}, {"y", 2}, {"z", 3}};
  formula_0.constant_ = 5;
  formula_0.type_ = ArithmeticFormula::Type::LT;

  EXPECT_EQ(6, formula_0.CountOnes(15));
  EXPECT_EQ(6, formula_0.CountOnes(7));
  EXPECT_EQ(3, formula_0.CountOnes(3));
  EXPECT_EQ(4, formula_0.CountOnes(5));

  formula_0.variable_coefficient_map_["xx"] = 0;
  formula_0.variable_coefficient_map_["yy"] = 0;
  formula_0.variable_coefficient_map_["zz"] = 0;

  EXPECT_EQ(6, formula_0.CountOnes(15));
  EXPECT_EQ(6, formula_0.CountOnes(7));
  EXPECT_EQ(3, formula_0.CountOnes(3));
  EXPECT_EQ(4, formula_0.CountOnes(5));
}

//TEST_F(ArithmeticFormulaTest, IsVariableOrderingSame) {
//  std::map<std::string ,int> eq_1 = {{"x", 0}, {"z", 1}, {"y", 2}};
//  std::vector<int> coeff = {1, 2, 3};
//
//  ArithmeticFormula formula_1(variable_coefficient_map_, coefficients);
//  ArithmeticFormula formula_2(eq_1, coeff);
//
//  EXPECT_TRUE(formula_1.IsVariableOrderingSame(&formula_1));
//  EXPECT_FALSE(formula_1.IsVariableOrderingSame(&formula_2));
//}
//
//TEST_F(ArithmeticFormulaTest, MergeCoefficients) {
//  std::vector<int> coeff_1 = {-1, -2, -3};
//  std::vector<int> coeff_3 = {-1, 1, 3, 5, 7};
//  std::map<std::string ,int> eq_1 = {{"x", 0}, {"y", 1}, {"z", 2}};
//  std::map<std::string ,int> eq_2 = {{"y", 0}, {"z", 1}, {"x", 2}};
//  std::map<std::string ,int> eq_3 = {{"a", 0}, {"y", 1}, {"b", 2}, {"z", 3}, {"c", 4}};
//
//  ArithmeticFormula formula_0(variable_coefficient_map_, coefficients);
//  ArithmeticFormula formula_1(eq_1, coeff_1);
//  ArithmeticFormula formula_2(eq_2, coeff_1);
//  ArithmeticFormula formula_3(eq_3, coeff_3);
//
//  formula_0.MergeCoefficients(&formula_1);
//  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("x", 0), Pair("y", 1), Pair("z", 2)));
//  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(1, 2, 3)); // do not update coefficients
//
//  formula_0.MergeCoefficients(&formula_2);
//  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("y", 0), Pair("z", 1), Pair("x", 2)));
//  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(2, 3, 1)); // do not update coefficients
//
//  formula_0.MergeCoefficients(&formula_3);
//  EXPECT_THAT(formula_0.get_coefficient_index_map(), UnorderedElementsAre(Pair("a", 0), Pair("y", 1), Pair("b", 2), Pair("z", 3), Pair("c", 4), Pair("x", 5)));
//  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(0, 2, 0, 3, 0, 1)); // do not update coefficients
//}
//
//TEST_F(ArithmeticFormulaTest, ResetCoefficients) {
//  ArithmeticFormula formula_0(variable_coefficient_map_, coefficients);
//  formula_0.reset_coefficients();
//
//  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(0, 0, 0));
//
//  formula_0.reset_coefficients(3);
//  EXPECT_THAT(formula_0.get_coefficients(), ElementsAre(3, 3, 3));
//}


} /* namespace Test */
} /* namespace Theory */
} /* namespace Vlab */
