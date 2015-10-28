/*
 * Path.h
 *
 *  Created on: Oct 29, 2015
 *      Author: baki
 */

#ifndef TEST_HELPER_PATH_H_
#define TEST_HELPER_PATH_H_

#define PP_STRINGIZE(text) #text
#define STRINGIZE(text) PP_STRINGIZE(text)

namespace Vlab {
namespace Test {
namespace Path {

const static std::string ABC_PATH = STRINGIZE(__ABC_PATH__);
const static std::string TEST_PATH = ABC_PATH + "/test";
const static std::string FIXTURE_PATH = TEST_PATH + "/fixtures";
const static std::string EXPECTATION_PATH = TEST_PATH + "/expectations";
const static std::string THEORY_E_PATH = EXPECTATION_PATH + "/theory";

}
} /* namespace Test */
} /* namespace Vlab */

#endif /* TEST_HELPER_PATH_H_ */
