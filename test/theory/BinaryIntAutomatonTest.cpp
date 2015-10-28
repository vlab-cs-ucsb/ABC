/*
 * BinaryIntAutomatonTest.cpp
 *
 *  Created on: Oct 29, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "BinaryIntAutomatonTest.h"

namespace Vlab {
namespace Theory {
namespace Test {

using namespace ::testing;
using namespace Vlab::Test::Path;
using namespace Vlab::Test::Mock;

void BinaryIntAutomatonTest::SetUp() {
  std::vector<int> coefficients = {1,2,3};
  std::map<std::string, int> coeff_index_map = {{"x", 0}, {"y", 1}, {"z", 2}};
  formula = new ArithmeticFormula(coeff_index_map, coefficients);
  formula->setType(ArithmeticFormula::Type::EQ);
  formula->setConstant(7);
}

void BinaryIntAutomatonTest::TearDown() {
  delete formula;
}

TEST_F(BinaryIntAutomatonTest, EmptyConstructor) {
  BinaryIntAutomaton b_int_auto;
  EXPECT_EQ(Automaton::Type::BINARYINT, b_int_auto.getType());
  EXPECT_EQ(nullptr, b_int_auto.getFormula());
  EXPECT_EQ(nullptr, b_int_auto.getDFA());
}

TEST_F(BinaryIntAutomatonTest, ConstructorWithArgs) {
  BinaryIntAutomaton b_int_auto(nullptr, 5);
  EXPECT_EQ(Automaton::Type::BINARYINT, b_int_auto.getType());
  EXPECT_EQ(nullptr, b_int_auto.getFormula());
  EXPECT_EQ(nullptr, b_int_auto.getDFA());
  EXPECT_EQ(5, b_int_auto.getNumberOfVariables());
}

TEST_F(BinaryIntAutomatonTest, CopyConstructor) {
  BinaryIntAutomaton_ptr auto_1 = BinaryIntAutomaton::makeAutomaton(formula->clone());
  BinaryIntAutomaton auto_2 = BinaryIntAutomaton( *auto_1 );

  EXPECT_NE(auto_1->getFormula(), auto_2.getFormula());
  EXPECT_THAT(auto_1->getFormula()->str(), auto_2.getFormula()->str());
  EXPECT_NE(auto_1->getDFA(), auto_2.getDFA());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, Complement) {
  std::stringstream ss;
    std::string expected;
    TestableBinaryIntAutomaton testable_binary_automaton;
    BinaryIntAutomaton_ptr auto_1 = nullptr;
    BinaryIntAutomaton_ptr auto_2 = nullptr;
    ArithmeticFormula formula_0;
    formula_0.setVariableCoefficient("x", 1);
    formula_0.setConstant(-3);
    formula_0.setType(ArithmeticFormula::Type::EQ);

    auto_1 = testable_binary_automaton.makeEquality(formula_0.clone());
    auto_2 = auto_1->complement();
    auto_2->toDot(ss);
    expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_01.dot");
    EXPECT_THAT(expected, ss.str());
    EXPECT_EQ(ArithmeticFormula::Type::NOTEQ, auto_2->getFormula()->getType());
    delete auto_1;
    delete auto_2;


    formula_0.setConstant(3);
    auto_1 = testable_binary_automaton.makeEquality(formula_0.clone());
    auto_2 = auto_1->complement();

    ss.str("");
    auto_2->toDot(ss);
    expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_02.dot");
    EXPECT_THAT(expected, ss.str());
    EXPECT_EQ(ArithmeticFormula::Type::NOTEQ, auto_2->getFormula()->getType());
    delete auto_1;
    delete auto_2;

    ArithmeticFormula formula_1;
    formula_1.setVariableCoefficient("x", 1);
    formula_1.setVariableCoefficient("y", 2);
    formula_1.setConstant(-6);
    formula_1.setType(ArithmeticFormula::Type::NOTEQ);
    auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_1.clone());
    auto_2 = auto_1->complement();

    ss.str("");
    auto_2->toDot(ss);
    expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_03.dot");
    EXPECT_THAT(expected, ss.str());
    EXPECT_EQ(ArithmeticFormula::Type::EQ, auto_2->getFormula()->getType());
    delete auto_1;
    delete auto_2;

    formula_1.setVariableCoefficient("y", -2);
    auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_1.clone());
    auto_2 = auto_1->complement();

    ss.str("");
    auto_2->toDot(ss);
    expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_04.dot");
    EXPECT_THAT(expected, ss.str());
    EXPECT_EQ(ArithmeticFormula::Type::EQ, auto_2->getFormula()->getType());
    delete auto_1;
    delete auto_2;
}

TEST_F(BinaryIntAutomatonTest, Intersect) {
  std::stringstream ss;
    std::string expected;
    TestableBinaryIntAutomaton testable_binary_automaton;
    BinaryIntAutomaton_ptr auto_1 = nullptr;
    BinaryIntAutomaton_ptr auto_2 = nullptr;
    BinaryIntAutomaton_ptr auto_3 = nullptr;
    ArithmeticFormula formula_0;
    formula_0.setVariableCoefficient("x", 1);
    formula_0.setConstant(-3);
    formula_0.setType(ArithmeticFormula::Type::GE);

    ArithmeticFormula formula_1;
    formula_1.setVariableCoefficient("y", 2);
    formula_1.setConstant(-6);
    formula_1.setType(ArithmeticFormula::Type::NOTEQ);

    ArithmeticFormula formula_2;
    formula_2.setVariableCoefficient("x", 1);
    formula_2.setConstant(-3);
    formula_2.setType(ArithmeticFormula::Type::LE);

    auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());
    auto_2 = testable_binary_automaton.makeAutomaton(formula_1.clone());
    EXPECT_DEATH(auto_1->intersect(auto_2), ".*You cannot intersect binary automata with different variable orderings.*");
    delete auto_2;

    auto_2 = testable_binary_automaton.makeAutomaton(formula_2.clone());
    auto_3 = auto_1->intersect(auto_2);
    delete auto_1;
    delete auto_2;

    formula_0.setType(ArithmeticFormula::Type::EQ);
    auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());

    EXPECT_EQ(ArithmeticFormula::Type::INTERSECT, auto_3->getFormula()->getType());

    auto_2 = auto_3->difference(auto_1);
    EXPECT_TRUE(auto_2->isEmptyLanguage());

    delete auto_1;
    delete auto_2;
    delete auto_3;
}

TEST_F(BinaryIntAutomatonTest, Union) {
  std::stringstream ss;
    std::string expected;
    TestableBinaryIntAutomaton testable_binary_automaton;
    BinaryIntAutomaton_ptr auto_1 = nullptr;
    BinaryIntAutomaton_ptr auto_2 = nullptr;
    BinaryIntAutomaton_ptr auto_3 = nullptr;
    ArithmeticFormula formula_0;
    formula_0.setVariableCoefficient("x", 1);
    formula_0.setConstant(-3);
    formula_0.setType(ArithmeticFormula::Type::LT);

    ArithmeticFormula formula_1;
    formula_1.setVariableCoefficient("y", 2);
    formula_1.setConstant(-6);
    formula_1.setType(ArithmeticFormula::Type::NOTEQ);

    ArithmeticFormula formula_2;
    formula_2.setVariableCoefficient("x", 1);
    formula_2.setConstant(-3);
    formula_2.setType(ArithmeticFormula::Type::GT);

    auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());
    auto_2 = testable_binary_automaton.makeAutomaton(formula_1.clone());
    EXPECT_DEATH(auto_1->intersect(auto_2), ".*You cannot intersect binary automata with different variable orderings.*");
    delete auto_2;

    auto_2 = testable_binary_automaton.makeAutomaton(formula_2.clone());
    auto_3 = auto_1->union_(auto_2);

    delete auto_1;
    delete auto_2;

    formula_0.setType(ArithmeticFormula::Type::NOTEQ);
    auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());

    EXPECT_EQ(ArithmeticFormula::Type::UNION, auto_3->getFormula()->getType());
    auto_2 = auto_3->difference(auto_1);
    EXPECT_TRUE(auto_2->isEmptyLanguage());

    delete auto_1;
    delete auto_2;
    delete auto_3;
}

TEST_F(BinaryIntAutomatonTest, Difference) {
  std::stringstream ss;
  std::string expected;
  std::string actual;
  TestableBinaryIntAutomaton testable_binary_automaton;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  BinaryIntAutomaton_ptr auto_2 = nullptr;
  BinaryIntAutomaton_ptr auto_3 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::LE);

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setConstant(-3);
  formula_1.setType(ArithmeticFormula::Type::LT);

  auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());
  auto_2 = testable_binary_automaton.makeAutomaton(formula_1.clone());
  auto_3 = auto_1->difference(auto_2);

  delete auto_1;
  delete auto_2;

  formula_0.setType(ArithmeticFormula::Type::EQ);
  auto_1 = testable_binary_automaton.makeAutomaton(formula_0.clone());

  auto_2 = auto_3->difference(auto_1);
  EXPECT_TRUE(auto_2->isEmptyLanguage());

  delete auto_1;
  delete auto_2;
  delete auto_3;
}

TEST_F(BinaryIntAutomatonTest, MakeEquality) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  TestableBinaryIntAutomaton testable_binary_automaton;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::EQ);


  auto_1 = testable_binary_automaton.makeEquality(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = testable_binary_automaton.makeEquality(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::EQ);
  auto_1 = testable_binary_automaton.makeEquality(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = testable_binary_automaton.makeEquality(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeEquality_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeNotEquality) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::NOTEQ);

  auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::NOTEQ);
  auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = TestableBinaryIntAutomaton::makeNotEquality(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeNotEquality_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeLessThan) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::LT);

  auto_1 = TestableBinaryIntAutomaton::makeLessThan(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThan_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = TestableBinaryIntAutomaton::makeLessThan(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThan_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::LT);
  auto_1 = TestableBinaryIntAutomaton::makeLessThan(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThan_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = TestableBinaryIntAutomaton::makeLessThan(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThan_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeLessThanOrEqual) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::LE);

  auto_1 = TestableBinaryIntAutomaton::makeLessThanOrEqual(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThanOrEqual_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = TestableBinaryIntAutomaton::makeLessThanOrEqual(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThanOrEqual_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::LE);
  auto_1 = TestableBinaryIntAutomaton::makeLessThanOrEqual(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThanOrEqual_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = TestableBinaryIntAutomaton::makeLessThanOrEqual(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeLessThanOrEqual_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeGreaterThan) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::GT);

  auto_1 = TestableBinaryIntAutomaton::makeGreaterThan(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThan_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThan(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThan_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::GT);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThan(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThan_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThan(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThan_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeGreaterThanOrEqual) {
  std::stringstream ss;
  std::string expected;
  BinaryIntAutomaton_ptr auto_1 = nullptr;
  ArithmeticFormula formula_0;
  formula_0.setVariableCoefficient("x", 1);
  formula_0.setConstant(-3);
  formula_0.setType(ArithmeticFormula::Type::GE);

  auto_1 = TestableBinaryIntAutomaton::makeGreaterThanOrEqual(formula_0.clone());

  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThanOrEqual_01.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_0.setConstant(3);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThanOrEqual(formula_0.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThanOrEqual_02.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  ArithmeticFormula formula_1;
  formula_1.setVariableCoefficient("x", 1);
  formula_1.setVariableCoefficient("y", 2);
  formula_1.setConstant(-6);
  formula_1.setType(ArithmeticFormula::Type::GE);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThanOrEqual(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThanOrEqual_03.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;

  formula_1.setVariableCoefficient("y", -2);
  auto_1 = TestableBinaryIntAutomaton::makeGreaterThanOrEqual(formula_1.clone());

  ss.str("");
  auto_1->toDot(ss);
  expected = Vlab::Test::FileHelper::getExpectation("theory", "BinaryIntAutomaton", "makeGreaterThanOrEqual_04.dot");
  EXPECT_THAT(expected, ss.str());
  delete auto_1;
}

TEST_F(BinaryIntAutomatonTest, MakeAutomaton) {
  std::vector<int> coeff = {1};
  std::map<std::string, int> indexes = {{"x", 0}};
  ArithmeticFormula formula_0(indexes, coeff);
  formula_0.setConstant(3);
  formula_0.setType(ArithmeticFormula::Type::NONE);

  EXPECT_DEATH(TestableBinaryIntAutomaton::BinaryIntAutomaton::makeAutomaton(formula_0.clone()), ".*Equation type is not specified, please set type for input formula.*");

  // TODO mocking will allow us to write call expectations
}



} /* namespace Test */
} /* namespace Theory */
} /* namespace Vlab */
