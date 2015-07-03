/*
 * StringBuilder.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "StringBuilder.h"

namespace Vlab {
namespace Util {

StringBuilder::StringBuilder() {
}

StringBuilder::~StringBuilder() {
}

template<typename T>
StringBuilder& StringBuilder::operator <<(const T& data) {
  ss << data;
  return *this;
}

StringBuilder::operator std::string() {
  return ss.str();
}

} /* namespace Util */
} /* namespace Vlab */
