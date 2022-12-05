import React from "react";
import { NextSeo, DefaultSeo } from "next-seo";
import PropTypes from "prop-types";
/**
 * SEO component
 * @param {Object} props
 * @component
 */
const Seo = (props) => {
  const {
    title,
    canonical,
    titleTemplate = "%s | Linaro Mui Web",
    ...rest
  } = props;
  return (
    <NextSeo
      titleTemplate={titleTemplate}
      defaultTitle={title}
      canonical={canonical}
      {...rest}
    />
  );
};
Seo.propTypes = {
  title: PropTypes.string,
  titleTemplate: PropTypes.string,
  canonical: PropTypes.string,
};

/**
 * Default SEO settings.
 * @param {Object} props
 */
export const SeoDefaults = (props) => {
  const { defaultTitle, description, canonical, ...rest } = props;
  return (
    <DefaultSeo
      defaultTitle={defaultTitle}
      description={description}
      canonical={canonical}
      {...rest}
    />
  );
};
SeoDefaults.propTypes = {
  defaultTitle: PropTypes.string,
  description: PropTypes.string,
  canonical: PropTypes.string,
};

export default Seo;
