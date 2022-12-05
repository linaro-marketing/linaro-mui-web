// Generated with util/create-component.js
import React from "react";
import Link from "next/link";
import Box from "@mui/material/Box";
import { LinkedProps } from "./Linked.types";
const Linked: React.FC<LinkedProps> = React.forwardRef((props, ref) => {
  const { to, textLink, options, target = null, ...rest } = props;
  return (
    <Link
      href={{
        pathname: to,
        ...options,
      }}
    >
      <Box
        component="a"
        {...rest}
        sx={[
          { color: "inherit" },
          textLink && {
            color: (theme) => theme.palette.primary.main,
          },
        ]}
        ref={ref}
        target={
          to.startsWith("/") && !target ? "_self" : target ? target : "_blank"
        }
        href={to}
      />
    </Link>
  );
});
export default Linked;
