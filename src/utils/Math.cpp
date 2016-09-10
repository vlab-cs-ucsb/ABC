/*
 * Math.cpp
 *
 *  Created on: Nov 16, 2015
 *      Author: baki
 */

#include "Math.h"

namespace Vlab {
namespace Util {
namespace Math {

int gcd(int x, int y) {
  if (x == 0) {
    return std::abs(y);
  }
  int c;
  while (y != 0) {
    c = x % y;
    x = y;
    y = c;
  }
  return std::abs(x);
}

int lcm(int x, int y) {
  return x * y / gcd(x, y);
}

Matrix multiply_matrix(const Matrix& x, const Matrix& y) {
  unsigned r = x[0].size();
  unsigned c = y.size();

  Matrix result(r, std::vector<boost::multiprecision::cpp_int> (c, 0));
  for (unsigned i = 0; i < r; ++i) {
    for (unsigned k = 0; k < r; ++k) {
      for (unsigned j = 0; j < c; ++j) {
        result[i][j] += x[i][k] * y[k][j];
      }
    }
  }

  return result;
}

Matrix multiply_matrix_multi_thread(const Matrix& x, const Matrix& y) {
  const unsigned row_size = x[0].size();
  const unsigned column_size = y.size();

  Matrix result(row_size, std::vector<boost::multiprecision::cpp_int> (column_size, 0));

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

  return result;
}

} /* namespace Math */
} /* namespace Util */
} /* namespace Vlab */
