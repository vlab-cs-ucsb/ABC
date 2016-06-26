//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation()
    : type_(Type::NONE),
      trackmap_handle_(nullptr) {
  num_tracks_ = 0;
}

StringRelation::StringRelation(Type t, std::map<std::string, int>* trackmap,
                               std::vector<Subrelation> subrels, size_t ntracks)
    : type_(t),
      trackmap_handle_(trackmap),
      subrelations_(subrels),
      num_tracks_(ntracks) {
}

StringRelation::~StringRelation() {
  DVLOG(VLOG_LEVEL) << "Bye";
}

StringRelation::StringRelation(const StringRelation &other)
    : type_(other.type_),
      trackmap_handle_(other.trackmap_handle_),
      subrelations_(other.subrelations_),
      num_tracks_(other.num_tracks_) {
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
    case Type::VAR:
      ss << "<var>";
      break;
    case Type::CONSTANT:
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

void StringRelation::set_num_tracks(size_t ntracks) {
  this->num_tracks_ = ntracks;
}

size_t StringRelation::get_num_tracks() const {
  return this->trackmap_handle_->size();
}

int StringRelation::get_variable_index(std::string name) {
  if(trackmap_handle_ == nullptr) {
    LOG(FATAL) << "Cannot get variable index: no trackmap set in relation for variable: " << name;
  }

  auto iter = trackmap_handle_->find(name);
  if (iter == trackmap_handle_->end()) {
    DVLOG(VLOG_LEVEL) << "No index for: " << name;
    return -1;
  }
  return iter->second;
}

std::map<std::string ,int>* StringRelation::get_term_trackmap() {
  return trackmap_handle_;
}

bool StringRelation::has_same_trackmap(StringRelation_ptr other_relation) {
  if (trackmap_handle_ not_eq other_relation->trackmap_handle_) {
    return false;
  }

  return true;
}

//TODO: Check if the relations are equal...
StringRelation_ptr StringRelation::combine(StringRelation_ptr other_relation) {
  StringRelation_ptr result_relation = nullptr;
  std::vector<Subrelation> subrels(this->subrelations_);
  subrels.insert(subrels.end(), other_relation->subrelations_.begin(), other_relation->subrelations_.end());
  result_relation = new StringRelation(StringRelation::Type::INTERSECT, this->trackmap_handle_, subrels,
                                       this->trackmap_handle_->size());
  return result_relation;
}

void StringRelation::add_subrelation(StringRelation::Subrelation subrel) {
  this->subrelations_.push_back(subrel);
}

std::vector<StringRelation::Subrelation> StringRelation::get_subrelation_list() {
  return subrelations_;
}

std::map<std::string, int>* StringRelation::get_variable_trackmap() {
  return this->trackmap_handle_;
}

void StringRelation::set_variable_trackmap(std::map<std::string, int>* trackmap) {
  this->trackmap_handle_ = trackmap;
}

std::ostream& operator<<(std::ostream& os, const StringRelation& relation) {
  return os << relation.str();
}

} /* namespace Theory */
} /* namespace Vlab */
