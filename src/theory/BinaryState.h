/*
 * BinaryState.h
 *
 *  Created on: Nov 7, 2015
 *      Author: baki
 */

#ifndef SRC_THEORY_BINARYSTATE_H_
#define SRC_THEORY_BINARYSTATE_H_

namespace Vlab {
namespace Theory {

class BinaryState {
public:

  enum class Type :
        int { NONE = 0, VAL, REMT, REMF };

  BinaryState();
  BinaryState(Type t, int v, int b);
  BinaryState(int v, int b);
  virtual ~BinaryState();

  Type getType();
  void setType(Type t);
  int getV();
  int getB();
  int getd0();
  int getd1();

  void setTypeValueBit(Type t, int v, int b);
  void setd0(int d0);
  void setd1(int d1);
  void setd0d1(int d0, int d1);

  bool isEqualTo(Type t, int v, int b);
  bool isEqualTo(int v, int b);
  bool isLeadingZeroState();
protected:
  Type type;
  int V;
  int B;
  int d0;
  int d1;
};

typedef BinaryState* BinaryState_ptr;

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_BINARYSTATE_H_ */
