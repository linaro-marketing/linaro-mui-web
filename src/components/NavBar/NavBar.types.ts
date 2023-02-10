import { AppBarProps } from "@mui/material";
import { MenuItem } from "components/DropdownMenuItem/DropdownMenuItem.types";
// Generated with util/create-component.js
export interface NavBarProps extends AppBarProps {
  /**
   * The link that the logo will point to.
   */
  logoLink: string;
  /**
   * The site title fallback if no logo is provided.
   */
  title?: string;
  /**
   * The logo to be displayed in the NavBar.
   */
  logo?: string;
  /**
   * The pages to be displayed in the NavBar.
   */
  pages: MenuItem[];
  /**
   * Dark mode toggle.
   */
  themeMode?: string;
  darkModeToggle?:boolean;
  /**
   * The function to be called when the theme mode is toggled.
   */
  toggleTheme?: () => void;
}
