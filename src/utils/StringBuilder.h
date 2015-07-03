/*
 * StringBuilder.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef UTILS_STRINGBUILDER_H_
#define UTILS_STRINGBUILDER_H_

#include <string>
#include <sstream>

namespace Vlab {
namespace Util {

class StringBuilder {
public:
  StringBuilder();
  virtual ~StringBuilder();

  template<typename T>
  StringBuilder& operator <<(const T& data);

  operator std::string();
protected:
  std::stringstream ss;
};

} /* namespace Util */
} /* namespace Vlab */

#endif /* UTILS_STRINGBUILDER_H_ */
