//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation()
    : type_(Type::NONE),
      left_(nullptr),
      right_(nullptr),
      data_(""),
      trackmap_handle_(nullptr) {
  DVLOG(VLOG_LEVEL) << "HELLO : " << str();
}

StringRelation::StringRelation(Type t, StringRelation_ptr left, StringRelation_ptr right,
                std::string data, std::map<std::string, int>* trackmap)
    : type_(t),
      left_(left),
      right_(right),
      data_(data),
      trackmap_handle_(trackmap) {
  DVLOG(VLOG_LEVEL) << "HELLO : " << str();
}

StringRelation::~StringRelation() {
  DVLOG(VLOG_LEVEL) << "BYEBYE : " << str();
  if(left_) delete left_;
  if(right_) delete right_;
}

StringRelation::StringRelation(const StringRelation &other) {
  this->type_ = other.type_;
  if(other.left_ != nullptr) {
    this->left_ = other.left_->clone();
  } else {
    this->left_ = nullptr;
  }
  if(other.right_ != nullptr) {
    this->right_ = other.right_->clone();
  } else {
    this->right_ = nullptr;
  }
  this->data_ = other.data_;
  this->trackmap_handle_ = other.trackmap_handle_;
  DVLOG(VLOG_LEVEL) << "HELLO (CLONE) : " << str();
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

std::string StringRelation::str() const {
  std::stringstream ss;

  ss << "string relation: ";
  switch (type_) {
    case Type::EQ:
      ss << "=";
      break;
    case Type::NOTEQ:
      ss << "!=";
      break;
    case Type::GT:
      ss << ">";
      break;
    case Type::GE:
      ss << ">=";
      break;
    case Type::LT:
      ss << "<";
      break;
    case Type::LE:
      ss << "<=";
      break;
    case Type::INTERSECT:
      ss << "&";
      break;
    case Type::UNION:
      ss << "|";
      break;
    case Type::STRING_VAR:
      ss << "<var>";
      break;
    case Type::STRING_CONSTANT:
      ss << "<constant>";
      break;
    default:
      ss << "none";
      break;
  }

  return ss.str();
}

void StringRelation::set_type(Type type) {
  this->type_ = type;
}

StringRelation::Type StringRelation::get_type() const {
  return this->type_;
}

void StringRelation::set_left(StringRelation_ptr left) {
  this->left_ = left;
}
StringRelation_ptr StringRelation::get_left() {
  return this->left_;
}

void StringRelation::set_right(StringRelation_ptr right) {
  this->right_ = right;
}

StringRelation_ptr StringRelation::get_right() {
  return this->right_;
}

void StringRelation::set_data(std::string data) {
  this->data_ = data;
}

std::string StringRelation::get_data() {
  return this->data_;
}

int StringRelation::get_variable_index(std::string name) {
  if(trackmap_handle_ == nullptr) {
    LOG(FATAL) << "Cannot get variable index: no trackmap set in relation for variable: " << name;
  }

  auto iter = trackmap_handle_->find(name);
  if (iter == trackmap_handle_->end()) {
    return -1;
  }
  return iter->second;
}

bool StringRelation::has_same_trackmap(StringRelation_ptr other_relation) {
  if (trackmap_handle_ not_eq other_relation->trackmap_handle_) {
    return false;
  }

  return true;
}

std::map<std::string, int>* StringRelation::get_variable_trackmap() {
  return this->trackmap_handle_;
}

void StringRelation::set_variable_trackmap(std::map<std::string, int>* trackmap) {
  this->trackmap_handle_ = trackmap;
}

int StringRelation::get_num_tracks() {
  if(trackmap_handle_ == nullptr) {
    return 0;
  }
  return trackmap_handle_->size();
}

std::ostream& operator<<(std::ostream& os, const StringRelation& relation) {
  return os << relation.str();
}

} /* namespace Theory */
} /* namespace Vlab */
