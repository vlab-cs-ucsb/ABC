/*
 * Math.h
 *
 *  Created on: Nov 16, 2015
 *      Author: baki
 */

#ifndef SRC_UTILS_MATH_H_
#define SRC_UTILS_MATH_H_

#include <cstdlib>
#include <functional>
#include <thread>
#include <vector>

namespace Vlab {
namespace Util {
namespace Math {

template <class T>
using Matrix = std::vector<std::vector<T>>;

int gcd(int x, int y);
int lcm(int x, int y);

template <class T>
Matrix<T> multiply_matrix(const Matrix<T>& x, const Matrix<T>& y) {
  unsigned r = x[0].size();
  unsigned c = y.size();

  Matrix<T> result(r, std::vector<T> (c, 0));
  for (unsigned i = 0; i < r; ++i) {
    for (unsigned j = 0; j < c; ++j) {
      for (unsigned k = 0; k < r; ++k) {
        result[i][j] += x[i][k] * y[k][j];
      }
    }
  }

  return std::move(result);
}

template <class T>
Matrix<T> multiply_matrix_multi_thread(const Matrix<T>& x, const Matrix<T>& y) {
  const unsigned row_size = x[0].size();
  const unsigned column_size = y.size();

  Matrix<T> result(row_size, std::vector<T> (column_size, 0));

  const int cores = std::thread::hardware_concurrency();
  const int num_of_threads = cores;
  const int rows_per_thread = row_size / num_of_threads;
  int extra_rows = row_size % num_of_threads;
  unsigned start = 0;
  unsigned end = rows_per_thread;

  auto multiply_rows = [row_size, column_size, &result, &x, &y](unsigned start, unsigned end) -> void {
    for (unsigned i = start; i < end; ++i) {
      for (unsigned k = 0; k < row_size; ++k) {
        for (unsigned j = 0; j < column_size; ++j) {
          result[i][j] += x[i][k] * y[k][j];
        }
      }
    }
  };

  std::vector<std::thread> workers;
  for (int i = 0; i < num_of_threads; ++i) {
    if (0 < extra_rows) {
      end += 1;
      --extra_rows;
    }

    if (start == end) {
      break;
    }

    workers.push_back(std::thread(multiply_rows, start, end));

    start = end;
    end = start + rows_per_thread;
  }

  for (auto& t : workers) {
    t.join();
  }

  return std::move(result);
}

} /* namespace Math */
} /* namespace Util */
} /* namespace Vlab */

#endif /* SRC_UTILS_MATH_H_ */
