/*
 * ArithmeticFormula.h
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#ifndef SRC_THEORY_ARITHMETICFORMULA_H_
#define SRC_THEORY_ARITHMETICFORMULA_H_

#include <cmath>
#include <cstdlib>
#include <locale>
#include <map>
#include <sstream>
#include <string>
#include <vector>
#include <utility>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../utils/Math.h"

namespace Vlab
{
  namespace Theory
  {

    class ArithmeticFormula;
    using ArithmeticFormula_ptr = ArithmeticFormula*;

    class ArithmeticFormula
    {
       public:
        enum class Type
          :
          int
          {
            NONE = 0,
          EQ,
          NOTEQ,
          GT,
          GE,
          LT,
          LE,
          INTERSECT,
          UNION,
          VAR
        };

        struct CoefficientInfo
        {
            int minimum_sum_of_coefficients_;
            int maximum_sum_of_coefficients_;
            int number_of_zero_coefficients_;
            int constant_;
            std::vector<int> coefficients_;
        };

        ArithmeticFormula();
        virtual ~ArithmeticFormula();

        ArithmeticFormula(const ArithmeticFormula&);
        ArithmeticFormula_ptr clone() const;

        std::string str() const;
        void set_type(Type type);
        ArithmeticFormula::Type get_type() const;
        int get_number_of_variables() const;
        std::map<std::string, int> get_variable_coefficient_map() const;
        void set_variable_coefficient_map(std::map<std::string, int>& coefficient_map);
        int get_variable_coefficient(std::string) const;
        void set_variable_coefficient(std::string, int coeff);
        void add_variable(std::string, int);
        std::vector<int> get_coefficients() const;
        int get_constant() const;
        void set_constant(int constant);
        bool is_constant() const;
        void reset_coefficients(int value = 0);
        int get_variable_index(std::string) const;
        std::string get_variable_at_index(const std::size_t index) const;

        bool has_relation_to_mixed_term(const std::string var_name) const;
        void add_relation_to_mixed_term(const std::string var_name, const ArithmeticFormula::Type relation,
                                        const SMT::Term_ptr term);
        std::pair<ArithmeticFormula::Type, SMT::Term_ptr> get_relation_to_mixed_term(const std::string var_name) const;
        bool UpdateMixedConstraintRelations();

        ArithmeticFormula_ptr Add(ArithmeticFormula_ptr);
        ArithmeticFormula_ptr Subtract(ArithmeticFormula_ptr);
        ArithmeticFormula_ptr Multiply(int value);
        ArithmeticFormula_ptr negate();

        /**
         * Sets all coefficients to 0 except the given variable which is set to 1.
         * And sets the value of the given variable to given value.
         * @param var_name
         * @param value
         * @return
         */
        ArithmeticFormula_ptr ToConstantVariableFormula(const std::string var_name, const int value) const;

        /**
         * Converts GT, GE, and LE into LT equivalent formula.
         * @return
         */
        ArithmeticFormula_ptr ToLessThanEquivalentFormula();

        /**
         * Returns coefficient info for the formula.
         * @return
         */
        const CoefficientInfo GetCoefficientInfo() const;

        bool Simplify();
        int CountOnes(unsigned long n) const;
        void merge_variables(const ArithmeticFormula_ptr other);

        friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

       protected:
        bool get_var_names_if_equality_of_two_vars(std::string &v1, std::string &v2);

        ArithmeticFormula::Type type_;
        int constant_;
        std::map<std::string, int> variable_coefficient_map_;

        // TODO a quick solution for a restricted set of cases in mixed constraints
        // generalize it as much as possible
        std::map<std::string, std::pair<ArithmeticFormula::Type, SMT::Term_ptr>> mixed_terms_;

       private:
        static const int VLOG_LEVEL;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
