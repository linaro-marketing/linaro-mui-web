// Generated with util/create-component.js
import React from "react";
import Link from "next/link";
import Box from "@mui/material/Box";
import { LinkedProps } from "./Linked.types";
/**
 * @param {LinkedProps} props
 * @returns {JSX.Element}
 */
const Linked: React.FC<LinkedProps> = React.forwardRef((props, ref) => {
  const { to, textLink, options, children, target = null, ...rest } = props;
  return (
    <Box
      component={Link}
      {...rest}
      sx={[
        { color: "inherit" },
        textLink && { "&:hover": { color: "primary.main" } },
      ]}
      ref={ref}
      target={
        to.startsWith("/") && !target ? "_self" : target ? target : "_blank"
      }
      href={to}
      children={children}
    />
  );
});
export default Linked;
